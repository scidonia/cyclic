#!/usr/bin/env python3
"""LLM-based oracle for the supercompiler.

Three modes of operation:

1. LIBRARY mode (imported by test_llm_generalise.py):
       from llm_generalise import generalise, propose_lemma
       result = generalise(current, companion, context, memo)
       lemma  = propose_lemma(stuck_config, wrapper_context, companion, history)

2. SERVE mode (called by the OCaml extraction shim):
       echo '<json>' | python llm_generalise.py --serve
   Reads one JSON request from stdin, writes one JSON response to stdout.
   The OCaml shim (llm_oracle_impl.ml) uses this mode.

3. SERVE-LEMMA mode (called when SC needs auxiliary lemma):
       echo '<json>' | python llm_generalise.py --serve-lemma

4. DEMO mode (no flags):
       python llm_generalise.py
   Runs a built-in example.

JSON request schema (serve):
  {
    "current":    "<term string>",
    "companion":  "<term string>",
    "context":    "<type context string>",
    "memo":       ["<term string>", ...]
  }

JSON request schema (serve-lemma):
  {
    "stuck":          "<current stuck term>",
    "wrapper_context": "<f[·]> the context pattern separating stuck from companion",
    "companion":      "<companion term from memo table>",
    "history":        ["<term>", ...]    # driving history
  }

JSON response schema (success):
  {
    "gen":              "<generalised term string>",
    "sigma_current":    ["<term>", ...],
    "sigma_companion":  ["<term>", ...],
    "attempts":         <int>
  }

JSON response schema (lemma):
  {
    "lemma":            "<lemma statement>",
    "hypothesis":       "<hypothesis needed>"  (or null if unconditional),
    "justification":    "<why this lemma helps>",
    "attempts":         <int>
  }

JSON response schema (failure / LLM gives up):
  { "gen": null }
  { "lemma": null }
"""

import json
import os
import sys


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

def build_prompt(current_term: str, companion_term: str,
                 context: str, memo_entries: list) -> str:
    memo_str = "\n".join(f"  - {t}" for t in memo_entries) or "  (none)"
    return f"""You are a supercompilation expert. The supercompiler is stuck: \
syntactic anti-unification cannot generalise the two configurations below. \
Your task is to propose a SEMANTICS-AWARE generalisation (cut formula).

CURRENT configuration (stuck, needs generalisation):
  {current_term}
  Context: {context}

COMPANION configuration (previous vertex in memo table):
  {companion_term}

Other memo entries:
{memo_str}

Propose a GENERALISED configuration S_gen and substitutions sigma (for \
current) and sigma0 (for companion) such that:
  current  = sigma(S_gen)
  companion = sigma0(S_gen)

Guidelines:
- Abstract over the DIFFERING subterms (typically function arguments or \
list elements).
- Exploit known fusion/optimisation identities when applicable:
    map f (map g l) = map (f . g) l
    length (map f l) = length l
    sum (map f l) = fold_right (fun x acc => f x + acc) 0 l
    filter p (map f l) = map_filter f p l
- The generalised term must be a valid typing judgement in the same signature.
- Prefer the MOST SPECIFIC generalisation that still enables folding.

Example: if current = "f (cons a l)" and companion = "f l", then:
  gen             = "f ?0"           (introduce hole ?0 for the list argument)
  sigma_current   = ["cons a l"]     (substitute ?0 := cons a l in current)
  sigma_companion = ["l"]            (substitute ?0 := l in companion)

Respond ONLY with valid JSON — no prose, no markdown fences:
{{
  "gen": "the generalised term (with ?0, ?1, ... for holes)",
  "sigma_current": ["value for ?0 in current", "value for ?1 in current", ...],
  "sigma_companion": ["value for ?0 in companion", "value for ?1 in companion", ...]
}}

Both sigma lists MUST be non-empty (at least one hole).
If no useful generalisation exists, respond with:
{{"gen": null}}"""


# ---------------------------------------------------------------------------
# LLM call
# ---------------------------------------------------------------------------

def call_llm(prompt: str) -> str | None:
    """Call DeepSeek V4 Pro (or fallback model) and return raw text."""
    api_key = os.environ.get("DEEPSEEK_API_KEY", "")
    model   = os.environ.get("LLM_MODEL", "deepseek-chat")

    if not api_key:
        print("=== LLM PROMPT ===", file=sys.stderr)
        print(prompt, file=sys.stderr)
        print("=== END PROMPT ===", file=sys.stderr)
        print("Set DEEPSEEK_API_KEY to enable LLM calls.", file=sys.stderr)
        return None

    try:
        from openai import OpenAI
        client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")
        response = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system",
                 "content": "You are a supercompilation expert. "
                             "Respond only with valid JSON."},
                {"role": "user", "content": prompt},
            ],
            temperature=0.3,
            max_tokens=600,
        )
        return response.choices[0].message.content
    except ImportError:
        print("Install openai: pip install openai", file=sys.stderr)
        return None


# ---------------------------------------------------------------------------
# Response parsing
# ---------------------------------------------------------------------------

def parse_response(text: str | None) -> dict:
    if text is None:
        return {"gen": None}
    try:
        # Strip markdown fences if the model wraps the JSON
        if "```json" in text:
            text = text.split("```json")[1].split("```")[0]
        elif "```" in text:
            text = text.split("```")[1].split("```")[0]
        return json.loads(text.strip())
    except json.JSONDecodeError:
        return {"gen": None, "error": "Failed to parse LLM response",
                "raw": text}


# ---------------------------------------------------------------------------
# Kernel validation stub
# ---------------------------------------------------------------------------

def validate_candidate(gen, sigma_current, sigma_companion) -> tuple[bool, str]:
    """Lightweight pre-check before sending to the Rocq kernel.

    In production, the Rocq kernel performs the authoritative check via
    [trace_condition_ok].  This stub catches obvious malformed proposals
    early, reducing round-trips.
    """
    if gen is None:
        return False, "gen is null"
    errors = []
    if not sigma_current:
        errors.append("sigma_current is empty")
    if not sigma_companion:
        errors.append("sigma_companion is empty")
    if errors:
        return False, "; ".join(errors)
    return True, ""


# ---------------------------------------------------------------------------
# Main entry point (with retry)
# ---------------------------------------------------------------------------

def generalise(current: str, companion: str,
               context: str | None = None,
               memo: list | None = None,
               max_retries: int = 3) -> dict:
    """Propose a generalisation for *current* and *companion*.

    Returns a dict with keys:
      "gen"             — the generalised term string (or None)
      "sigma_current"   — substitution list for current
      "sigma_companion" — substitution list for companion
      "attempts"        — number of LLM calls made
    """
    prompt = build_prompt(
        current, companion,
        context or "unknown",
        memo or [],
    )

    for attempt in range(1, max_retries + 1):
        raw  = call_llm(prompt)
        result = parse_response(raw)

        if result.get("gen") is None:
            # LLM gave up or errored; no point retrying unless there was a
            # parse error (the LLM didn't follow the format).
            if result.get("error") == "Failed to parse LLM response":
                prompt = (
                    f"Your previous response could not be parsed as JSON. "
                    f"Error: {result.get('raw', '')}\n\n"
                    f"Please respond with ONLY valid JSON. "
                    f"Original task: generalise '{current}' and '{companion}'."
                )
                continue
            result["attempts"] = attempt
            return result

        gen       = result.get("gen")
        sigma_c   = result.get("sigma_current", [])
        sigma_p   = result.get("sigma_companion", [])
        valid, err = validate_candidate(gen, sigma_c, sigma_p)

        if valid:
            result["attempts"] = attempt
            return result

        # Feed the error back to the LLM and retry
        prompt = (
            f"Your proposal was rejected: {err}\n\n"
            f"Original task: generalise '{current}' and '{companion}'.\n"
            f"Respond with valid JSON only."
        )

    return {"gen": None, "attempts": max_retries,
            "error": "Max retries exceeded"}


# ---------------------------------------------------------------------------
# Lemma proposal (omega-rule / conditional CIU)
# ---------------------------------------------------------------------------

def build_lemma_prompt(stuck_term: str, wrapper_context: str,
                       companion_term: str, history: list) -> str:
    history_str = "\n".join(f"  - {t}" for t in (history or [])) or "  (none)"
    return f"""You are a supercompilation expert. The supercompiler is stuck \
because a recursive call is blocked by a "wrapper context" that appears between \
the current configuration and its companion. A lemma about this wrapper would \
unblock the proof.

CURRENT stuck configuration:
  {stuck_term}

COMPANION configuration (in memo table, would fold to this):
  {companion_term}

WRAPPER CONTEXT (the function f[·] that separates current from companion):
  {wrapper_context}

Driving history:
{history_str}

The supercompiler wants to fold the current config back to the companion, \
but cannot because the wrapper f[·] prevents the match. If f preserves the \
property being checked, a lemma makes the fold go through.

Propose an AUXILIARY LEMMA that, if proved, would enable the fold.

Examples of useful lemmas:
  sorted l → sorted (insert x l) = true    (insert preserves sortedness)
  plus 0 n = n                             (zero is left-identity of plus)
  length l = n → length (take k l) = min k n  (take refines length)
  rev (append l1 l2) = append (rev l2) (rev l1)  (append-distribution for rev)

Respond with the lemma in this JSON format:
{{
  "lemma": "the lemma statement as a string",
  "hypothesis": "the hypothesis needed" (or null if unconditional),
  "justification": "why this lemma unblocks the fold"
}}

If no useful lemma exists, respond:
{{"lemma": null}}"""


def propose_lemma(stuck_term: str, wrapper_context: str,
                  companion_term: str, history: list | None = None,
                  max_retries: int = 2) -> dict:
    """Propose an auxiliary lemma to unblock the SC.

    Returns a dict with keys:
      "lemma"         — the lemma statement (or None)
      "hypothesis"    — the hypothesis needed (or None)
      "justification" — why this lemma helps
      "attempts"      — number of LLM calls made
    """
    prompt = build_lemma_prompt(
        stuck_term, wrapper_context, companion_term,
        history or []
    )

    for attempt in range(1, max_retries + 1):
        raw = call_llm(prompt)
        result = parse_response(raw)

        if result.get("lemma") is None:
            if result.get("error") == "Failed to parse LLM response":
                prompt = (
                    f"Your previous response could not be parsed as JSON. "
                    f"Error: {result.get('raw', '')}\n\n"
                    f"Please respond with ONLY valid JSON. "
                    f"Propose a lemma for: stuck='{stuck_term}', "
                    f"companion='{companion_term}', wrapper='{wrapper_context}'."
                )
                continue
            result["attempts"] = attempt
            return result

        lemma = result.get("lemma")
        if lemma and len(lemma) > 3:  # non-trivial lemma
            result["attempts"] = attempt
            return result

        prompt = (
            f"Your proposal was too trivial (len={len(lemma)}). "
            f"Original task: stuck='{stuck_term}', "
            f"companion='{companion_term}', wrapper='{wrapper_context}'.\n"
            f"Respond with a substantial lemma in valid JSON."
        )

    return {"lemma": None, "attempts": max_retries,
            "error": "Max retries exceeded"}


def serve_lemma() -> None:
    """Read lemma request from stdin, write JSON response to stdout."""
    try:
        data = json.load(sys.stdin)
    except json.JSONDecodeError as e:
        json.dump({"lemma": None, "error": f"Invalid JSON input: {e}"},
                  sys.stdout)
        return

    result = propose_lemma(
        data.get("stuck", ""),
        data.get("wrapper_context", ""),
        data.get("companion", ""),
        data.get("history", []),
        max_retries=data.get("max_retries", 2),
    )
    json.dump(result, sys.stdout)

def serve() -> None:
    """Read one JSON request from stdin, write one JSON response to stdout."""
    try:
        data = json.load(sys.stdin)
    except json.JSONDecodeError as e:
        json.dump({"gen": None, "error": f"Invalid JSON input: {e}"},
                  sys.stdout)
        return

    result = generalise(
        data.get("current",   ""),
        data.get("companion", ""),
        data.get("context"),
        data.get("memo", []),
        max_retries=data.get("max_retries", 3),
    )
    json.dump(result, sys.stdout)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if "--serve-lemma" in sys.argv:
        serve_lemma()
    elif "--serve" in sys.argv:
        serve()
    else:
        # Demo: lemma proposal
        lemma = propose_lemma(
            stuck_term="sorted (insert x (sort xs))",
            wrapper_context="sorted (insert x [·])",
            companion_term="sorted (sort xs)",
            history=[
                "sorted (sort (cons x xs))",
                "sorted (insert x (sort xs))",
            ],
        )
        print("=== Lemma proposal ===")
        print(json.dumps(lemma, indent=2))
        print()
        # Demo: nested map fusion
        gen = generalise(
            current="length (map f (map g xs))",
            companion="length (map f (map g l))",
            context="l xs : List Nat, f g : Nat → Nat",
            memo=["length (map f (map g l)) : Nat"],
        )
        print("=== Generalisation ===")
        print(json.dumps(gen, indent=2))
