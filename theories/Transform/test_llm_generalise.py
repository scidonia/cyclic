#!/usr/bin/env python3
"""Test harness: run supercompiler, identify where generalisation fails,
   call LLM for better generalisation, compare results."""

import json
import os
import subprocess
import sys

def run_supercompiler(term_str):
    """Run Rocq on a test program and extract the cfg_builder state."""
    # This is a stub - in practice you'd parse the Rocq output
    pass

def main():
    # Example: nested map fusion
    current = "length (map f (map g xs))"
    companion = "length (map f (map g l))"
    
    from llm_generalise import generalise
    
    print("=" * 60)
    print("Testing LLM generalisation for nested map fusion")
    print("=" * 60)
    print(f"\nCurrent:  {current}")
    print(f"Companion: {companion}")
    print(f"\nExpected optimal: length (map (f ∘ g) l)")
    print(f"Current best_generalize produces: length (map f (map g H))")
    
    result = generalise(
        current, companion,
        context="l : List, f : Nat→Nat, g : Nat→Nat, xs : List",
        memo=["length (map f (map g l)) : Nat"]
    )
    
    print(f"\nLLM result: {json.dumps(result, indent=2)}")
    
    if result.get("gen"):
        print(f"\n✓ LLM proposed generalisation: {result['gen']}")
        print(f"  σ_current: {result.get('sigma_current', [])}")
        print(f"  σ_companion: {result.get('sigma_companion', [])}")
    else:
        print("\n✗ LLM did not propose a generalisation")


if __name__ == "__main__":
    main()
