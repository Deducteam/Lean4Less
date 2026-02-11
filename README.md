# Lean4Less

Lean4Less is a tool for translating Lean to smaller theories (generically referred to by the name "Lean-") by "eliminating" certain definitional equalities through the insertion of explicit typecasts with type equality proof terms constructed using representative propositional equality theorems. It is a modification of [Lean4Lean](https://github.com/digama0/lean4lean), a port of Lean's C++ typechecker code into Lean.

The purpose of Lean4Less is to help ease the translation of proofs from Lean to other systems (e.g. Coq), but it can hopefully also be extended to enable some limited form of (simulated) extensional reasoning in Lean, as it implements a translation framework consistent with a general extensional to intensional translation (formalized by Winterhalter et. al. in [ett-to-itt](https://github.com/TheoWinterhalter/ett-to-itt), see [this related paper](https://dl.acm.org/doi/10.1145/3293880.3294095)).

Paper: [Lean4Less: Eliminating Definitional Equalities from Lean via an Extensional-to-Intensional Translation](https://inria.hal.science/hal-05310102)

Also, here are [some slides I presented at ICTAC 2025](https://rish987.github.io/files/lean4less_slides.pdf)

## Overview

Lean4Less is currently capable of eliminating proof irrelevance (PI) and K-like reduction (KLR) in Lean via through the use of a proof irrelevance theorem:

```lean
-- proof irrelevance, represented as an explicit propositional equality theorem
theorem prfIrrel {P : Prop} (p q : P) : p = q := ...
```

To do so, it "patches" the terms to insert type casts (a.k.a. transports) using generated equality proofs to ensure that terms have the expected type in Lean- (when enforced by typing constraints or by type annotation).

For instance, the following typechecks in Lean via proof irrelevance:
```lean
-- `T p` is defeq to `T q` in Lean (due to proof irrelevance)
def ex1 {P : Prop} {T : P → Type} (p q : p) (t : T p) : T q := t
```
By injecting typecasts, we can translate this to Lean- as follows:
```lean
theorem congrArg {A : Sort u} {B : Sort v} {x y : A}
(f : A → B) (h : x = y) : f x = f y := ...

def cast {A B : Sort u} (h : A = B) (a : A) : B := ...

def ex1' {P : Prop} {T : P → Type} (p q : P) (t : T p) : T q :=
  cast (congrArg T (prfIrrel p q)) t
```

As a more complex example, the following nested use of proof irrelevance:

```lean
def ex2 {P : Prop} {Q : P → Prop} {T : (p : P) → Q p → Prop}
   (p q : p) (Qp : Q p) (Qq : Q q) (t : T p Qp) : T q Qq := t
```
can be translated to Lean- as:
```lean
-- need heterogeneous equality
inductive HEq : {A : Sort u} → A →
    {B : Sort u} → B → Prop where
  | refl (a : A) : HEq a a

theorem appHEq {A B : Type u}
  {U : A → Type v} {V : B → Type v}
  {f : (a : A) → U a} {g : (b : B) → V b}
  {a : A} {b : B} (hAB : A = B)
  (hUV : (a : A) → (b : B)
    → HEq a b → HEq (U a) (V b))
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := ...

theorem eq_of_heq {A : Sort u} {a a' : A}
  (h : HEq a a') : a = a' := ...

-- (proved via `prfIrrel`)
theorem prfIrrelPQ {P Q : Prop} (h : P = Q)
  (p : P) (q : Q) : HEq p q := ...

def ex2' {P : Prop} {Q : P → Prop} {T : (p : P) → Q p → Prop}
   (p q : P) (Qp : Q p) (Qq : Q q) (t : T p Qp) : T q Qq :=
  cast (eq_of_heq 
  (appHEq (congrArg Q (eq_of_heq (prfIrrelPQ rfl p q)))
    (fun _ _ _ => HEq.rfl)
    (appHEq rfl ... HEq.rfl (prfIrrelPQ rfl p q))
    (prfIrrelPQ (congrArg Q (eq_of_heq (prfIrrelPQ rfl p q)))
      Qp Qq))) t
```
(in general, Lean4Less uses the `HEq` type and custom congruence lemmas -- see [this file](patch/PatchTheorems.lean) for the full list of constants introduced by Lean4Less).

## Building

See [here](https://lean-lang.org/lean4/doc/quickstart.html) for how to install Lean and `elan`. With `elan` installed, compile Lean4Less by running:
```
lake build
```

Note that one of Lean4Less's dependencies is a fork of Lean4Lean (found [here](https://github.com/rish987/lean4lean/tree/lean4less)) that it uses for output verification (as well as some optimizations during translation).

## Running

After `lake build`, the Lean4Less executable can be found in `.lake/build/bin/lean4less`.

The command line arguments are:

> `lean4less [--proof-irrel] [--klike-red] [--only const] [--print] [--cached cache_dir] [MOD]`

* `MOD`: a required lean module name to load the environment for translation, like `Init.Classical`.
* `--proof-irrel` (`-pi`): Eliminate proof irrelevance.
* `--klike-red` (`-klr`): Eliminate K-like reduction.
* `--only` (`-o`): Only translate the specified constants and their dependencies (output as an `.olean` file to directory `only_out/` with a filename corresponding to the name of the constant).
* `--print` (`-p`): Print translated constant specified by --only.
* `--cached` (`-c`): Use cached library translation files from specified directory.

If `--only` is not specified, the translated environment, consisting of the translations of all of the constants in `MOD` + all of its imported modules, is output in the directory `out/` as `.olean` files. The output file structure mirrors that of the input, with the addition of an `Init.PatchPrelude` module (imported by `Init.Prelude`) isolating the [translation-specific definitions](patch/PatchTheorems.lean) and their dependencies.

NOTE: with recent changes to Lean's `.olean` module system, the `.olean` output functionality is currently broken.

You can run the executable using `lake exe`. For instance, to translate the standard library to Lean-, run:
```
 $ lake exe lean4less -pi -klr Std
```
The translation will be output to an `out/` directory, which will also contain an `aborted.txt` file containing a list of constants whose translation was aborted (see caveats section below).

To translate only the definition `Classical.em` and see its translation, run:
```
 $ lake exe lean4less Std -klr -pi --only Classical.em --print
```
which will create the file `only_out/Classical.em.olean`.

To continue an interrupted translation, you can use the `-c` option, (e.g. `lean4less -pi -klr Std -c out`).

To translate a different Lean package, navigate the directory of the target project, then use `lake env path/to/lean4lean/.lake/build/bin/lean4less <args>` to run `lean4less` in the context of the target project, for example:
```
 $ (cd ~/projects/mathlib4/ && lake env ~/projects/lean4less/.lake/build/bin/lean4less -klr -pi Mathlib.Data.Real.Basic)
```

## Verification

After translation, Lean4Less will perform a verification run on the translated environment using a specialized fork of Lean4Lean, with the specified eliminated definitional equalities disabled.
See [the README of that fork](https://github.com/rish987/lean4lean/tree/lean4less) for details on how to run it on its own.

## Caveats/Limitations
* The translation unfortunately does not currently scale beyond small libraries (e.g. the Lean standard library `Std`) or lower modules in the Mathlib import hierarchy (e.g. `Mathlib.Data.Ordering.Basic`). When attempting to translate higher-level modules, the translation will probably get stuck at some point/run out of memory. This is likely due to large intermediate terms appearing and accumulating in the output as a consequence of K-like reduction. This issue may be alleviated through the generation of auxiliary constants as a part of translation, though this has not been implemented yet.
* There are some instances of translation where the output can "explode" in size, particularly when annotated types must themselves be patched, resulting in a kind of "transport hell". For example, the following definition produces a very large translation:
```lean
inductive K : Prop where
| mk : K

def F : Bool → Type
| true => Bool
| _ => Unit

structure S : Type where
b : Bool
f : F b

def projTest {B : Bool → Type} (s : B (S.mk true true).2)
   : B (@K.rec (fun _ => S) (S.mk true true) k).2 := s
```
This is an issue inherent to the translation, and so it is not possible to optimize the output to avoid it. However, it can perhaps be alleviated by minimizing unnecessary uses of proof irrelevance on the input side (prior to translation).
* Lean4Less may insert casts where they are not strictly necessary -- that is, within terms that are already well-typed in Lean-. This is because it is based on the implementation of Lean's typechecker, where the proof irrelevance check also functions as an optimization that short-circuits further definitional equality checking on proofs of the same propositional type. To avoid inserting such unnecessary casts during translation, it may seem like a good idea to first check if proof terms are already defeq in Lean-. However, attempting this proved to be prohibitively expensive in the worst case (when they are not defeq in Lean-, and must be fully expanded to compare them completely). We compromise by [placing a low limit](https://github.com/rish987/lean4lean/blob/fecb7ba619d99104951388942a2d54979c9eed30/Lean4Less/TypeChecker.lean#L1257) on the maximum recursion depth for this check.
* Attempting to eliminate just proof irrelevance and not K-like reduction as well will likely result in deep recursion (a.k.a. nontermination) at some point during output verification. It seems that this is due to the typechecker implementation performing K-like reduction too "eagerly" when proof irrelevance is disabled; further investigation is needed here.
* For now, we abort the translation of any constants whose typing requires large `Nat.gcd` computations, as well as that of any of their dependent constants. This is because for the equation `Nat.gcd (succ y) x = Nat.gcd (mod x (succ y)) (succ y)` to hold definitionally in Lean, the typechecker must use K-like reduction -- meaning that it does *not* hold definitionally in Lean-. As a consequence, it is not sound to override `Nat.gcd` with a primitive operation in the Lean- kernel, and so Lean4Less also does not treat `Nat.gcd` as primitive. So, for the moment we simply abort the translation of any constants that attempt to perform large `Nat.gcd` computations, to protect against runaway reduction when typechecking them with the Lean- kernel. You can find the list of aborted constants in the `out/aborted.txt` file. Fixing this issue will likely require manually patching the definition of `Nat.gcd` and its dependencies to no longer rely on K-like reduction for its defining equations to hold definitionally.
* The code isn't very well-documented yet.

Pull requests are welcome. Please open an issue/ping me on Zulip if you encounter any errors during translation.
