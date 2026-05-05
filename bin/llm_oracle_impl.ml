(** OCaml implementation of [LLM.llm_generalise].

    This module bridges the extracted Coq supercompiler and the Python LLM
    oracle script [llm_generalise.py].

    At runtime it:
    1. Serialises the stuck configuration and candidates to JSON.
    2. Forks [python3 llm_generalise.py --serve] and pipes the JSON in.
    3. Parses the JSON response back into a [gen_result].
    4. Returns [Some gen_result] on success, [None] if the LLM gives up.

    SOUNDNESS: the Rocq kernel never sees this code.  Only
    [Parameter LLM.llm_generalise] is visible to the proof checker.
    [trace_condition_ok] rejects any bad residual regardless of what we return.

    REMAINING STUB: [parse_gen_str] converts the LLM's string representation
    back into a [tm].  The LLM already uses de Bruijn holes (?0, ?1, ...) and
    the extracted [tm] constructors, so this is straightforward parsing of the
    S-expression grammar.  See [parse_gen_str] below.
*)

(** ------------------------------------------------------------------ *)
(** Pretty-printer: [tm] → string for the LLM prompt.
    Uses the same ?n notation the LLM echoes back, so round-tripping works. *)

(* These module aliases match what Coq's extraction produces for the
   Cyclic.Transform.LLMOracle module.  Adjust if the extracted module name
   differs. *)
module Tm = struct
  (* The extracted [tm] type — constructors match Term.Syntax *)
  type tm = LLMOracle.tm0
  let tVar n   = LLMOracle.TVar n
  let tApp f a = LLMOracle.TApp (f, a)
  let tLam a b = LLMOracle.TLam (a, b)
end

let rec pp_tm (t : LLMOracle.tm0) : string =
  match t with
  | LLMOracle.TVar n          -> Printf.sprintf "?%d" n
  | LLMOracle.TApp (f, a)     ->
      let rec collect_args acc t =
        match t with
        | LLMOracle.TApp (f, a) -> collect_args (a :: acc) f
        | _                     -> (t, acc)
      in
      let (head, args) = collect_args [a] f in
      let parts = List.map pp_tm (head :: args) in
      "(" ^ String.concat " " parts ^ ")"
  | LLMOracle.TLam (_, b)     -> Printf.sprintf "(lam. %s)" (pp_tm b)
  | LLMOracle.TFix (_, b)     -> Printf.sprintf "(fix. %s)" (pp_tm b)
  | LLMOracle.TCase (i,s,_,_) -> Printf.sprintf "(case[%d] %s ...)" i (pp_tm s)
  | LLMOracle.TRoll (i,c,_)   -> Printf.sprintf "(roll[%d,%d] ...)" i c
  | LLMOracle.TSort _         -> "Sort"
  | LLMOracle.TPi (_, b)      -> Printf.sprintf "(Pi. %s)" (pp_tm b)

let pp_config (j : LLMOracle.config) : string =
  match j with
  | LLMOracle.JTy (_, t, _)    -> pp_tm t
  | LLMOracle.JEq (_, t, u, _) ->
      Printf.sprintf "%s ≈ %s" (pp_tm t) (pp_tm u)
  | LLMOracle.JSub _           -> "<sub>"

(** ------------------------------------------------------------------ *)
(** JSON request builder *)

let json_escape (s : string) : string =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf {|\"|}
    | '\\' -> Buffer.add_string buf {|\\|}
    | '\n' -> Buffer.add_string buf {|\n|}
    | c    -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let build_request (current : LLMOracle.config)
    (cands : (LLMOracle.config * int) list) : string =
  let companion_str =
    match cands with [] -> "none" | (j, _) :: _ -> pp_config j
  in
  let memo_items =
    cands
    |> List.map (fun (j, _) ->
        Printf.sprintf {|"%s"|} (json_escape (pp_config j)))
    |> String.concat ","
  in
  Printf.sprintf
    {|{"current":"%s","companion":"%s","memo":[%s],"max_retries":2}|}
    (json_escape (pp_config current))
    (json_escape companion_str)
    memo_items

(** ------------------------------------------------------------------ *)
(** Minimal JSON field extraction (no external dependencies) *)

(** Find the value of [key] in a flat JSON object.
    Handles string values only; returns None for null / missing. *)
let json_str_field (key : string) (json : string) : string option =
  let pat = Printf.sprintf {|"%s":"|} key in
  let klen = String.length pat in
  let jlen = String.length json in
  let rec scan i =
    if i + klen > jlen then None
    else if String.sub json i klen = pat then
      let start = i + klen in
      let rec find_end j =
        if j >= jlen then None
        else if json.[j] = '\\' then find_end (j + 2)  (* skip escape *)
        else if json.[j] = '"'  then
          Some (String.sub json start (j - start))
        else find_end (j + 1)
      in
      find_end start
    else scan (i + 1)
  in
  scan 0

let json_is_null (key : string) (json : string) : bool =
  let pat = Printf.sprintf {|"%s":null|} key in
  let klen = String.length pat in
  let jlen = String.length json in
  let rec scan i =
    if i + klen > jlen then false
    else if String.sub json i klen = pat then true
    else scan (i + 1)
  in
  scan 0

(** Extract a JSON array of strings: ["a","b",...] *)
let json_str_array (key : string) (json : string) : string list =
  let pat = Printf.sprintf {|"%s":[|} key in
  let klen = String.length pat in
  let jlen = String.length json in
  let rec scan i =
    if i + klen > jlen then []
    else if String.sub json i klen = pat then
      (* parse strings until ] *)
      let pos = ref (i + klen) in
      let results = ref [] in
      (try while !pos < jlen do
        (* skip whitespace and commas *)
        while !pos < jlen && (json.[!pos] = ' ' || json.[!pos] = ','
                               || json.[!pos] = '\n') do
          incr pos
        done;
        if !pos >= jlen || json.[!pos] = ']' then raise Exit;
        if json.[!pos] = '"' then begin
          incr pos;
          let start = !pos in
          while !pos < jlen && json.[!pos] <> '"' do
            if json.[!pos] = '\\' then pos := !pos + 2
            else incr pos
          done;
          results := String.sub json start (!pos - start) :: !results;
          incr pos  (* skip closing quote *)
        end else
          raise Exit
      done with Exit -> ());
      List.rev !results
    else scan (i + 1)
  in
  scan 0

(** ------------------------------------------------------------------ *)
(** String → tm parser for LLM output.

    The LLM uses the grammar:
      term ::= ?n                    (de Bruijn hole / variable)
             | (term term ...)      (application spine)
             | (lam. term)          (lambda)
             | (fix. term)          (fixpoint)
             | name                  (known combinator by name — not used)

    We map ?n → TVar n.
    Application spines (f a b) → TApp (TApp f a) b.
    Everything else → TVar 0 (safe fallback; trace_condition_ok will reject
    the resulting graph if the fold doesn't type-check).
*)

let parse_gen_str (s : string) : LLMOracle.tm0 =
  let s = String.trim s in
  let len = String.length s in
  let pos = ref 0 in

  let skip_ws () =
    while !pos < len && (s.[!pos] = ' ' || s.[!pos] = '\n'
                          || s.[!pos] = '\t') do
      incr pos
    done
  in

  let rec parse_term () : LLMOracle.tm0 =
    skip_ws ();
    if !pos >= len then LLMOracle.TVar 0
    else match s.[!pos] with
    | '?' ->
        (* de Bruijn variable ?n *)
        incr pos;
        let start = !pos in
        while !pos < len && s.[!pos] >= '0' && s.[!pos] <= '9' do
          incr pos
        done;
        let n = int_of_string_opt (String.sub s start (!pos - start)) in
        LLMOracle.TVar (Option.value ~default:0 n)
    | '(' ->
        (* application spine or (lam. ...) or (fix. ...) *)
        incr pos;
        skip_ws ();
        (* Check for lam. / fix. *)
        let peek prefix =
          let plen = String.length prefix in
          !pos + plen <= len && String.sub s !pos plen = prefix
        in
        if peek "lam." then begin
          pos := !pos + 4;
          let body = parse_term () in
          skip_ws ();
          if !pos < len && s.[!pos] = ')' then incr pos;
          LLMOracle.TLam (LLMOracle.TSort 0, body)
        end else if peek "fix." then begin
          pos := !pos + 4;
          let body = parse_term () in
          skip_ws ();
          if !pos < len && s.[!pos] = ')' then incr pos;
          LLMOracle.TFix (LLMOracle.TSort 0, body)
        end else begin
          (* Application spine: (f a1 a2 ...) *)
          let head = parse_term () in
          let rec loop acc =
            skip_ws ();
            if !pos >= len || s.[!pos] = ')' then begin
              if !pos < len then incr pos;
              acc
            end else
              let arg = parse_term () in
              loop (LLMOracle.TApp (acc, arg))
          in
          loop head
        end
    | _ ->
        (* Unknown token — safe fallback *)
        while !pos < len && s.[!pos] <> ' ' && s.[!pos] <> ')'
              && s.[!pos] <> '(' do
          incr pos
        done;
        LLMOracle.TVar 0
  in
  parse_term ()

(** ------------------------------------------------------------------ *)
(** Subprocess call *)

let find_oracle_script () : string =
  let candidates = [
    Filename.concat (Filename.dirname Sys.executable_name) "llm_generalise.py";
    "theories/Transform/llm_generalise.py";
    "/home/gavin/dev/Scidonia/cyclic/theories/Transform/llm_generalise.py";
  ] in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> p
  | None   -> "llm_generalise.py"

let call_oracle (request_json : string) : string =
  let script = find_oracle_script () in
  let cmd = Printf.sprintf "python3 %s --serve" (Filename.quote script) in
  try
    let (ic, oc) = Unix.open_process cmd in
    output_string oc request_json;
    close_out oc;
    let buf = Buffer.create 256 in
    (try while true do Buffer.add_channel buf ic 1 done
     with End_of_file -> ());
    ignore (Unix.close_process (ic, oc));
    Buffer.contents buf
  with _ -> {|{"gen":null,"error":"subprocess failed"}|}

(** ------------------------------------------------------------------ *)
(** Lemma proposer — replaces [Parameter LLMLemmaProposer.llm_propose_lemma] *)

let build_lemma_request
    (stuck : LLMOracle.config)
    (companion : LLMOracle.config)
    (history : (LLMOracle.tm0 * LLMOracle.tm0) list) : string =
  let stuck_str     = json_escape (pp_config stuck) in
  let companion_str = json_escape (pp_config companion) in
  (* Extract the "wrapper context" from stuck vs companion — simplified:
     if stuck = f(companion) for some context f, the wrapper is f[·].
     For now we just use the stuck term as the wrapper hint. *)
  let wrapper_str = json_escape (pp_config stuck) in
  let history_items =
    history
    |> List.map (fun (t, _a) ->
        Printf.sprintf {|"%s"|} (json_escape (pp_tm t)))
    |> String.concat ","
  in
  Printf.sprintf
    {|{"stuck":"%s","wrapper_context":"%s","companion":"%s","history":[%s],"max_retries":2}|}
    stuck_str wrapper_str companion_str history_items

(** Parse a lemma string "lhs = rhs" into (lhs_tm, rhs_tm).
    Falls back to treating the whole string as lhs = tVar 0. *)
let parse_lemma_str (lemma_str : string) : (LLMOracle.tm0 * LLMOracle.tm0) option =
  try
    (* Try "lhs = rhs" split *)
    match String.split_on_char '=' lemma_str with
    | [lhs; rhs] ->
        let lhs_tm = parse_gen_str (String.trim lhs) in
        let rhs_tm = parse_gen_str (String.trim rhs) in
        Some (lhs_tm, rhs_tm)
    | _ ->
        (* No '=' found — just parse the whole string as lhs *)
        let tm = parse_gen_str (String.trim lemma_str) in
        Some (tm, LLMOracle.TVar 0)
  with _ -> None

let call_lemma_oracle (request_json : string) : string =
  let script = find_oracle_script () in
  let cmd = Printf.sprintf "python3 %s --serve-lemma" (Filename.quote script) in
  try
    let (ic, oc) = Unix.open_process cmd in
    output_string oc request_json;
    close_out oc;
    let buf = Buffer.create 256 in
    (try while true do Buffer.add_channel buf ic 1 done
     with End_of_file -> ());
    ignore (Unix.close_process (ic, oc));
    Buffer.contents buf
  with _ -> {|{"lemma":null,"error":"subprocess failed"}|}

(** The lemma record type — matches [LemmaEnv.lemma] from the Coq extraction.
    Since the OCaml shim is standalone (not generated by extraction), we
    define the type directly. *)
type lemma = { lemma_lhs : Tm.tm; lemma_rhs : Tm.tm }

let llm_propose_lemma
    (stuck : LLMOracle.config)
    (companion : LLMOracle.config)
    (history : (LLMOracle.tm0 * LLMOracle.tm0) list)
    : lemma option =
  let request = build_lemma_request stuck companion history in
  let response = call_lemma_oracle request in
  if json_is_null "lemma" response then None
  else
    match json_str_field "lemma" response with
    | None -> None
    | Some lemma_str ->
        match parse_lemma_str lemma_str with
        | None -> None
        | Some (lhs, rhs) ->
            Some {
              lemma_lhs = lhs;
              lemma_rhs = rhs;
            }

let llm_generalise
    (current : LLMOracle.config)
    (cands   : (LLMOracle.config * int) list)
    : LLMOracle.gen_result option =
  if cands = [] then None
  else begin
    let request = build_request current cands in
    let response = call_oracle request in
    if json_is_null "gen" response then None
    else
      match json_str_field "gen" response with
      | None -> None
      | Some gen_str ->
          let gen_tm = parse_gen_str gen_str in
          let sigma_c = json_str_array "sigma_current"  response in
          let sigma_p = json_str_array "sigma_companion" response in
          (* Build the generalised config — same type/context as current *)
          let gen_j =
            match current with
            | LLMOracle.JTy (ctx, _, a) -> LLMOracle.JTy (ctx, gen_tm, a)
            | other -> other
          in
          (* Convert sigma lists to [tm] lists using the same parser *)
          let to_tm_list = List.map parse_gen_str in
          Some {
            LLMOracle.gen_holes = [];          (* holes inferred from ?n vars *)
            LLMOracle.gen_j     = gen_j;
            LLMOracle.gen_sub1  = to_tm_list sigma_c;
            LLMOracle.gen_sub2  = to_tm_list sigma_p;
          }
  end
