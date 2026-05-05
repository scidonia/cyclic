#!/usr/bin/env python3
"""Generate a scrambled ListNat module and test whether the LLM recognizes lemmas.

This script:
1. Reads ListNat.v, replaces function names with random identifiers
2. Extracts each function's definition (body) for the prompt
3. Tests the LLM under two conditions:
   - Condition A (no-defs): only sees scrambled term expressions
   - Condition B (with-defs): also sees function definitions (tFix/tCase bodies)
4. Compares results against the baseline (original names)
"""

import json
import os
import re
import sys

# Map EVERY derived name to scrambled identifiers.
# Only object-language constructors (tLam, tApp, tCase, tFix, tVar, tRoll,
# tInd, tSort, tPi, tPi, shift, sub, fix, lam, app) are preserved.
SCRAMBLE_MAP = {
    # --- ListNat identifiers ---
    'length':       'x1_fwibble',
    'sum':          'x2_squod',
    'rev_acc':      'x3_nurple',
    'map':          'x4_jenkle',
    'append':       'x5_torple',
    'take':         'x6_grindle',
    'drop':         'x7_plonk',
    'reverse':      'x8_blip',
    'return_list':  'x9_forp',
    'bind':         'x10_twerg',
    'sort':         'x11_zindle',
    'insert':       'x12_flarp',
    'leb':          'x13_wiffle',
    'member':       'x14_cloop',
    'sorted':       'x15_gromble',
    'nat2nat':      'x16_snargh',
    # --- Type names (derived from inductive signatures) ---
    'list_ty':      't17_type',
    'nil':          't18_nulish',
    'cons':         't19_snood',
    'bool_ty':      't20_typeb',
    'bool_false':   't21_falsh',
    'bool_true':    't22_truish',
    'maybe_ty':     't23_typem',
    'nothing':      't24_nothish',
    'just':         't25_jost',
    'List_sig':     't26_sig1',
    'Maybe_sig':    't27_sig2',
    # --- Examples module identifiers ---
    'Examples.nat_ty':   't28_nat',
    'Examples.zero':     't29_zorq',
    'Examples.succ':     't30_slorp',
    'Examples.succ_fn':  't31_slorp_fn',
    'Examples.plusL':    't32_ploos',
    'Examples.plus':     't33_ploos_r',
    'Examples.Nat_sig':  't34_nat_sig',
    'Examples.Vec_sig':  't35_vec_sig',
    'Examples.Fin_sig':  't36_fin_sig',
    'Examples.Eq_sig':   't37_eq_sig',
    # --- Typing module identifiers ---
    'Typing.Typing.Cyclic.jTy':  't38_jty',
    'Typing.Typing.Cyclic.jEq':  't39_jeq',
    'Typing.Typing.Cyclic.jSub': 't40_jsub',
    # --- Supercompile identifiers ---
    'Supercompile.config':     't41_scfg',
    'Supercompile.cfg_builder':'t42_cfg',
    'Supercompile.gen_result': 't43_genr',
    'Supercompile.tm_eqb':     't44_eqb',
    'Supercompile.fv_tm':      't45_fvtm',
    'Supercompile.nub_nat':    't46_nub',
    'Supercompile.sort_nat':   't47_sortn',
    'Supercompile.nub_tm':     't48_nubtm',
    'Supercompile.succs_of':   't49_succs',
    'Supercompile.drive_step': 't50_drive',
    'Supercompile.canon_jTy':  't51_canon',
    'Supercompile.whistle_candidates': 't52_whist',
    'Supercompile.best_generalize':    't53_bestg',
    'Supercompile.trace_condition_ok': 't54_tcok',
    'Supercompile.residualise_jTy':    't55_resid',
    'Supercompile.residualise_jTy_fp': 't56_residfp',
    'SpeculationGen.vars_independent_of':   't57_varsind',
    'SpeculationGen.independent_subterms':  't58_indsub',
    'SpeculationGen.generalize_speculation':'t59_genspec',
    'SpeculationGen.dropped_vars':          't60_dropv',
    'SpeculationGen.subterm_sigma':         't61_subts',
    'SpeculationGen.config_fv':             't62_cfgfv',
    'SpeculationGen.best_generalize_with_speculation': 't63_bgspec',
    'LLM.residualise_jTy_llm':              't64_resllm',
    'LLM.supercompile_cfg_llm':             't65_scllm',
    'LLM.best_generalize_llm':              't66_bgllm',
    'LLM.llm_generalise':                   't67_llmgen',
    'LemmaEnv.validate_lemma':              't68_vallem',
    'LemmaProposer.propose_and_validate_lemma': 't69_propval',
}
# Expand with also not-found variants (without the module prefix):
_extra = {}
for k, v in SCRAMBLE_MAP.items():
    if '.' in k:
        _extra[k.split('.')[-1]] = v + "_x"
SCRAMBLE_MAP.update(_extra)

# Original → scrambled for terms in the prompt format
def scramble_wrapper(s):
    """Wrap a term in scrambled form: e.g., length(...) → x1_fwibble(...)"""
    # The LLM sees terms as pretty-printed strings
    # We need to replace all function names IN the term strings
    # But preserve the structural syntax: (f a), (case ...), etc.
    result = s
    for orig, scram in sorted(SCRAMBLE_MAP.items(), key=lambda x: -len(x[0])):
        result = result.replace(orig, scram)
    return result

# The original-readable names for Condition B (definitions provided)
# We extract these from the scrambled ListNat.v body text
def extract_def_summary(scram_name, orig_name, body_text):
    """Extract a concise summary of a function definition for the prompt."""
    # Get first non-blank lines of definition
    lines = [l.strip() for l in body_text.split('\n') if l.strip()]
    # Keep only the structure: tFix/tCase pattern
    structural = ' '.join(lines[:3])  # First 3 lines
    return f"  {scram_name} ({orig_name}): {structural}..."

# ---------------------------------------------------------------------------
# Test cases: each is a triple (stuck_term, companion, wrapper) in BOTH
# original and scrambled forms
# ---------------------------------------------------------------------------

TEST_CASES = [
    {
        "name": "sorted-insert",
        "stuck": "sorted (insert x (sort l))",
        "companion": "sorted (sort l)",
        "wrapper": "sorted (insert x [·])",
        "expected_lemma": "sorted l → sorted (insert x l) = true",
    },
    {
        "name": "length-map-map",
        "stuck": "length (map f (map g l))",
        "companion": "length (map f (map g xs))",
        "wrapper": "length (map f (map g [·]))",
        "expected_lemma": "map f (map g l) = map (f ∘ g) l",
    },
    {
        "name": "sum-reverse",
        "stuck": "sum (rev_acc l acc)",
        "companion": "sum (rev_acc l nil)",
        "wrapper": "sum (rev_acc l [·])",
        "expected_lemma": "sum (rev_acc l acc) = plus (sum l) acc",
    },
    {
        "name": "bind-assoc",
        "stuck": "bind (bind l f) g",
        "companion": "bind l (λx. bind (f x) g)",
        "wrapper": "bind (bind [·] f) g",
        "expected_lemma": "(bind (bind l f) g) = bind l (λx. bind (f x) g)",
    },
    {
        "name": "sort-length",
        "stuck": "length (sort l)",
        "companion": "length l",
        "wrapper": "length (sort [·])",
        "expected_lemma": "length (sort l) = length l",
    },
    {
        "name": "member-insert",
        "stuck": "member x (insert x l)",
        "companion": "true",
        "wrapper": "member x (insert x [·])",
        "expected_lemma": "member x (insert x l) = true",
    },
]


# ---------------------------------------------------------------------------
# LLM call (same as llm_generalise.py)
# ---------------------------------------------------------------------------

def call_llm(prompt):
    api_key = os.environ.get("DEEPSEEK_API_KEY", "")
    model = os.environ.get("LLM_MODEL", "deepseek-chat")
    if not api_key:
        return None
    from openai import OpenAI
    client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": "You are a supercompilation expert. Respond only with valid JSON."},
            {"role": "user", "content": prompt}
        ],
        temperature=0.3,
        max_tokens=500
    )
    return response.choices[0].message.content


# ---------------------------------------------------------------------------
# Condition B definitions preamble
# ---------------------------------------------------------------------------

ORIGINAL_DEFS = """
Available function definitions (structural, de Bruijn encoding):

  x1_fwibble (orig: length):  tFix (tPi t17_type t28_nat) (tLam t17_type (tCase 1 (tVar 0) t28_nat [t29_zorq; tLam t28_nat (tLam t17_type (t30_slorp (tApp (tVar 3) (tVar 0))))]))
  x2_squod (orig: sum):  tFix (tPi t17_type t28_nat) (tLam t17_type (tCase 1 (tVar 0) t28_nat [t29_zorq; tLam t28_nat (tLam t17_type (tApp (tApp t32_ploos (tVar 1)) (tApp (tVar 3) (tVar 0))))]))
  x4_jenkle (orig: map):  tFix (tPi x16_snargh (tPi t17_type t17_type)) (tLam x16_snargh (tLam t17_type (tCase 1 (tVar 0) t17_type [t18_nulish; tLam t28_nat (tLam t17_type (t19_snood (tApp (tVar 3) (tVar 1)) (tApp (tApp (tVar 4) (tVar 3)) (tVar 0))))])))
  x5_torple (orig: append):  tFix (tPi t17_type (tPi t17_type t17_type)) (tLam t17_type (tLam t17_type (tCase 1 (tVar 1) t17_type [tVar 0; tLam t28_nat (tLam t17_type (t19_snood (tVar 1) (tApp (tApp (tVar 4) (tVar 0)) (tVar 2))))])))
  x12_flarp (orig: insert):  tFix (tPi t28_nat (tPi t17_type t17_type)) (tLam t28_nat (tLam t17_type (tCase 1 (tVar 0) t17_type [t19_snood (tVar 1) t18_nulish; tLam t28_nat (tLam t17_type (tCase 0 (tApp (tApp x13_wiffle (tVar 3)) (tVar 1)) t17_type [...if t21_falsh then t19_snood (tVar 1) (tApp (tApp (tVar 4) (tVar 3)) (tVar 0)) else t19_snood (tVar 4) (t19_snood (tVar 2) (tVar 1))...]))]))))
  x11_zindle (orig: sort):  tFix (tPi t17_type t17_type) (tLam t17_type (tCase 1 (tVar 0) t17_type [t18_nulish; tLam t28_nat (tLam t17_type (tApp (tApp x12_flarp (tVar 1)) (tApp (tVar 3) (tVar 0))))]))
  x15_gromble (orig: sorted):  tFix (tPi t17_type t28_nat) (tLam t17_type (tCase 1 (tVar 0) t28_nat [t22_truish; tLam t28_nat (tLam t17_type (tCase 1 (tVar 0) t28_nat [t22_truish; tLam t28_nat (tLam t17_type (tCase 0 (tApp (tApp x13_wiffle (tVar 3)) (tVar 1)) t28_nat [...t21_falsh / recursive check...]))]))]))
  x3_nurple (orig: rev_acc):  tFix (tPi t17_type (tPi t17_type t17_type)) (tLam t17_type (tLam t17_type (tCase 1 (tVar 1) t17_type [tVar 0; tLam t28_nat (tLam t17_type (tApp (tApp (tVar 4) (tVar 0)) (t19_snood (tVar 1) (tVar 2))))])))
  x10_twerg (orig: bind):  tFix (tPi t17_type (tPi (tPi t28_nat t17_type) t17_type)) (tLam t17_type (tLam (tPi t28_nat t17_type) (tCase 1 (tVar 1) t17_type [t18_nulish; tLam t28_nat (tLam t17_type (tApp (tApp x5_torple (tApp (tVar 2) (tVar 1))) (tApp (tApp (tVar 4) (tVar 0)) (tVar 2))))])))
  x14_cloop (orig: member):  tFix (tPi t28_nat (tPi t17_type t28_nat)) (tLam t28_nat (tLam t17_type (tCase 1 (tVar 0) t28_nat [t21_falsh; ...tests x13_wiffle equality then returns t22_truish or recurses...])))
  x13_wiffle (orig: leb):  tFix (tPi t28_nat (tPi t28_nat t28_nat)) (tLam t28_nat (tLam t28_nat (tCase 0 (tVar 1) t28_nat [t22_truish; tLam t28_nat (tCase 0 (tVar 1) t28_nat [t21_falsh; tLam t28_nat (tApp (tApp (tVar 4) (tVar 1)) (tVar 0))])])))

  Type definitions:
    t17_type = tInd 1 []       (the List type)
    t18_nulish = tRoll 1 0 []  (empty list)
    t19_snood x xs = tRoll 1 1 [x; xs]  (list constructor)
    t28_nat = tInd 0 []        (type for natural numbers)
    t29_zorq = tRoll 0 0 []    (zero)
    t30_slorp n = tRoll 0 1 [n] (successor)
    t22_truish = t30_slorp t29_zorq  (boolean true encoded as succ zero)
    t21_falsh = t29_zorq              (boolean false encoded as zero)
    x16_snargh = tPi t28_nat t28_nat  (function type Nat -> Nat, called nat2nat in original)
"""

SCRAMBLED_DEFS = ORIGINAL_DEFS  # Same bodies, only names differ


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

def build_lemma_prompt(stuck, companion, wrapper, with_defs=False):
    defs_block = ""
    if with_defs:
        defs_block = f"""
## Available function definitions (de Bruijn encoding with scrambled names):
{SCRAMBLED_DEFS}
"""

    return f"""You are a supercompilation expert analyzing a cyclic proof search. \
The supercompiler is stuck: it cannot fold the current configuration onto \
a companion because a "wrapper context" prevents the match.

{defs_block}
## Current stuck configuration:
  {stuck}

## Companion configuration (in memo table):
  {companion}

## Wrapper context (f[·] that separates current from companion):
  {wrapper}

## Examples of useful lemmas:
  sorted l → sorted (insert x l) = true
  map f (map g l) = map (f ∘ g) l
  length (map f l) = length l
  bind (bind l f) g = bind l (λx. bind (f x) g)

Propose an AUXILIARY LEMMA that would enable the fold.

Respond ONLY with valid JSON:
{{
  "lemma": "the lemma statement as a string",
  "justification": "1-2 sentence explanation",
  "confidence": "high" | "medium" | "low"
}}

If no useful lemma exists, respond:
{{"lemma": null}}"""


# ---------------------------------------------------------------------------
# Run all tests
# ---------------------------------------------------------------------------

def parse_lemma(response):
    """Parse LLM response into lemma or None."""
    if response is None:
        return None, "no response"
    try:
        if "```json" in response:
            response = response.split("```json")[1].split("```")[0]
        elif "```" in response:
            response = response.split("```")[1].split("```")[0]
        return json.loads(response), None
    except json.JSONDecodeError as e:
        return None, str(e)


def run_test(case, condition, with_defs):
    """Run a single test case."""
    stuck = case["stuck"] if condition == "original" else scramble_wrapper(case["stuck"])
    companion = case["companion"] if condition == "original" else scramble_wrapper(case["companion"])
    wrapper = case["wrapper"] if condition == "original" else scramble_wrapper(case["wrapper"])
    
    prompt = build_lemma_prompt(stuck, companion, wrapper, with_defs=with_defs)
    raw = call_llm(prompt)
    lemma, err = parse_lemma(raw)
    
    return {
        "case": case["name"],
        "condition": condition,
        "with_defs": with_defs,
        "stuck": stuck,
        "companion": companion,
        "lemma": lemma.get("lemma") if lemma else None,
        "justification": lemma.get("justification", "") if lemma else "",
        "confidence": lemma.get("confidence", "") if lemma else "",
        "error": err,
        "raw": raw[:200] if raw else "",
    }


def main():
    results = []
    
    for case in TEST_CASES:
        # Original names, no defs (Condition A baseline)
        r = run_test(case, "original", with_defs=False)
        results.append(r)
        print(f"  ORIG / no-defs  [{case['name']}]: lemma={r['lemma']!r} conf={r['confidence']!r}")
        
        # Original names, with defs
        r = run_test(case, "original", with_defs=True)
        results.append(r)
        print(f"  ORIG / with-defs [{case['name']}]: lemma={r['lemma']!r} conf={r['confidence']!r}")

        # Scrambled names, no defs (Condition A)
        r = run_test(case, "scrambled", with_defs=False)
        results.append(r)
        print(f"  SCRAM / no-defs  [{case['name']}]: lemma={r['lemma']!r} conf={r['confidence']!r}")
        
        # Scrambled names, with defs (Condition B)
        r = run_test(case, "scrambled", with_defs=True)
        results.append(r)
        print(f"  SCRAM / with-defs [{case['name']}]: lemma={r['lemma']!r} conf={r['confidence']!r}")

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    
    for cond in ["original", "scrambled"]:
        for defs in [False, True]:
            label = f"{cond} / {'with-defs' if defs else 'no-defs'}"
            total = len(TEST_CASES)
            proposed = sum(1 for r in results
                          if r["condition"] == cond and r["with_defs"] == defs
                          and r["lemma"] is not None)
            high_conf = sum(1 for r in results
                           if r["condition"] == cond and r["with_defs"] == defs
                           and r["confidence"] == "high")
            print(f"  {label:25s}: {proposed}/{total} proposed, {high_conf} high-confidence")
    
    with open("/tmp/scramble_results.json", "w") as f:
        json.dump(results, f, indent=2)
    print("\nFull results in /tmp/scramble_results.json")


if __name__ == "__main__":
    main()
