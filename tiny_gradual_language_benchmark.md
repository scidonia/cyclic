# Tiny Gradual Language Benchmark

A minimal pure gradually typed language with typed dynamic errors.

## Types

```text
A, B ::= Nat | Bool | A -> B | ?
```

Every type has an explicit error inhabitant:

```text
err[A] : A
```

## Terms

```text
t ::= x
    | n
    | true | false
    | lam x:A. t
    | t u
    | if t then t else t
    | t + t
    | cast t A
    | err[A]
```

`cast t A` is a runtime type assertion.

## Core Reduction Rules

### Arithmetic

```text
n + m                  -> n+m
err[Nat] + t           -> err[Nat]
t + err[Nat]           -> err[Nat]
```

### Conditionals

```text
if true then t else u   -> t
if false then t else u  -> u
if err[Bool] then t else u -> err[A]
```

where both branches have type `A`.

### Functions

```text
(lam x:A. t) u          -> t[x := u]
err[A -> B] u           -> err[B]
```

### Casts

Successful casts:

```text
cast n Nat              -> n
cast true Bool          -> true
cast false Bool         -> false
cast (lam x:A. t) (A -> B)
                         -> lam x:A. cast t B
```

Failed casts:

```text
cast n Bool             -> err[Bool]
cast true Nat           -> err[Nat]
cast false Nat          -> err[Nat]
cast n (A -> B)         -> err[A -> B]
```

Error propagation through casts:

```text
cast err[A] B           -> err[B]
```

For the first benchmark, omit full dynamic boxing for `?`. Add it later if needed.

## Partial Evaluation Question

Can supercompilation / partial evaluation residualise closed terms directly to typed errors?

```text
supercompile t = err[A]
```

This would mean:

```text
t ≈CIU err[A]
```

So the dynamic type error has been discovered statically.

## Benchmark Goals

### 1. Obvious bad cast

```text
cast 3 Bool = err[Bool]
```

### 2. Error under context

```text
(cast 3 Bool) + 1 = err[Nat]
```

### 3. Error hidden behind beta reduction

```text
(lam x:Nat. x + 1) (cast true Nat) = err[Nat]
```

### 4. Error in conditional guard

```text
if (cast 0 Bool) then 1 else 2 = err[Nat]
```

### 5. Higher-order cast failure

```text
((lam f:Nat -> Nat. f 0) (cast 3 (Nat -> Nat))) = err[Nat]
```

### 6. Dead dynamic error should not fire

```text
if true then 1 else (cast false Nat) = 1
```

## Suggested Headline Example

```text
((lam f:Nat -> Nat. f 0) (cast 3 (Nat -> Nat))) + 1 = err[Nat]
```

This combines:

- higher-order functions
- casts
- typed errors
- beta reduction
- error propagation
- static discovery of dynamic failure

## Why This Is Useful

This benchmark tests whether partial evaluation is strong enough to expose dynamic type failures without running the full program. It is small, pure, and aligned with supercompilation: driving exposes reductions, while residual `err[A]` values represent statically discovered dynamic type errors.
