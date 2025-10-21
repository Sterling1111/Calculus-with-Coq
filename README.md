# Calculus with Coq

A formal, textbook-style development of single-variable calculus and supporting real analysis in the Coq proof assistant. The repository includes a reusable library (`Lib/`) plus worked problems for the Calculus track (`Calculus/`) and companion materials (`ATTAM/`).

## Highlights

Below are representative theorems with their exact Coq statements using this project's notations.

- Fundamental Theorem of Calculus — part I and II (file: `Lib/Integral.v`)

```coq
Theorem FTC1 : ∀ f a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ (λ x, ∫ a x f) [a, b] = f.

Theorem FTC1' : ∀ f a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ (λ x, ∫ x b f) [a, b] = - f.

Theorem FTC2 : ∀ a b f g,
    a < b -> continuous_on f [a, b] -> ⟦ der ⟧ g [a, b] = f -> ∫ a b f = g b - g a.
```

- Rolle’s and Mean Value Theorems — including Cauchy’s MVT (file: `Lib/Derivative.v`)

```coq
(* Rolle's Theorem *)
Theorem theorem_11_3 : forall f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f (a, b) -> f a = f b -> exists x, critical_point f (a, b) x.

(* Mean Value Theorem (one of its forms) *)
Theorem theorem_11_4 : forall f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f (a, b) -> exists x, x ∈ (a, b) /\ ⟦ der x ⟧ f = (λ _, (f b - f a) / (b - a)).

(* Cauchy Mean Value Theorem *)
Theorem cauchy_mvt : forall f f' g g' a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' -> 
    (forall x, x ∈ (a, b) -> g' x <> 0) -> g b <> g a -> exists x, x ∈ (a, b) /\ (f b - f a) / (g b - g a) = f' x / g' x.
```

- Intermediate Value Theorem (file: `Lib/Continuity.v`)

```coq
(* One-sided sign-change version implying zero in the interval *)
Theorem theorem_7_1 : forall f a b,
  a < b -> continuous_on f [a, b] -> f a < 0 < f b -> { x | x ∈ [a, b] /\ f x = 0 }.
```

- Completeness (Least Upper/Greatest Lower Bounds) toolkit (file: `Lib/Completeness.v`)

```coq
Lemma completeness_upper_bound : forall E:Ensemble ℝ,
  has_upper_bound E -> E ≠ ∅ -> { sup | is_lub E sup }.

Lemma completeness_lower_bound :
    forall E:Ensemble ℝ, has_lower_bound E -> E ≠ ∅ -> { inf | is_glb E inf }.

Lemma lub_unique : forall (E:Ensemble ℝ) a b, is_lub E a -> is_lub E b -> a = b.

Lemma glb_unique : forall (E:Ensemble ℝ) a b, is_glb E a -> is_glb E b -> a = b.
```

Additional substantial developments include limits and continuity laws (`Lib/Limit.v`, `Lib/Continuity.v`), derivatives and rules (`Lib/Derivative.v`), series and sequences (`Lib/Series.v`, `Lib/Sequence.v`), and a Riemann-style integral with partitions (`Lib/Integral.v`). The trigonometry module derives classical results from integral definitions.

### More notable lemmas and theorems

- Algebra/Combinatorics (file: `Lib/Binomial.v`)

```coq
Theorem Binomial_Theorem_R : forall a b n,
  (a + b) ^ n = sum_f 0 n (fun i => (choose n i) * a ^ (n - i) * b ^ i).
```

- Differentiation rules (file: `Lib/Derivative.v`)

```coq
(* Power rule *)
Theorem power_rule : forall n,
  ⟦ der ⟧ (fun x => x^n) = (fun x => INR n * x ^ (n - 1)).

(* Product rule (global form) *)
Theorem theorem_10_4_b : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.

(* Quotient rule (global form) *)
Theorem quotient_rule : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> (forall x, g x <> 0) ->
  ⟦ der ⟧ (f / g) = (g ∙ f' - f ∙ g')%f / (g ∙ g).

(* Chain rule (global form) *)
Theorem chain_rule : forall f g f' g',
  ⟦ der ⟧ g = g' -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ (f ∘ g) = ((f' ∘ g) ∙ g').
```

- Intermediate Value forms and consequences (file: `Lib/Continuity.v`)

```coq
(* Sign-change implies a zero (IVT-style) *)
Theorem theorem_7_1 : forall f a b,
  a < b -> continuous_on f [a, b] -> f a < 0 < f b -> { x | x ∈ [a, b] /\ f x = 0 }.

(* Full IVT: any c between f a and f b is achieved *)
Theorem theorem_7_4 : forall f a b c,
  a < b -> continuous_on f [a, b] -> f a < c < f b -> { x | x ∈ [a, b] /\ f x = c }.

Theorem theorem_7_5 : forall f a b c,
  a < b -> continuous_on f [a, b] -> f b < c < f a -> { x | x ∈ [a, b] /\ f x = c }.
```

- Extreme value and bounds on closed intervals (file: `Lib/Continuity.v`)

```coq
(* Maximum exists on [a,b] for continuous f *)
Theorem theorem_7_3 : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x1, x1 ∈ [a, b] /\ (forall x2, x2 ∈ [a, b] -> f x1 >= f x2).

(* Minimum exists on [a,b] for continuous f *)
Theorem theorem_7_7 : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x1, x1 ∈ [a, b] /\ (forall x2, x2 ∈ [a, b] -> f x1 <= f x2).
```

- Uniform continuity on compact intervals (file: `Lib/Continuity.v`)

```coq
Theorem theorem_8_A_1 : forall f a b,
  a <= b -> continuous_on f [a, b] -> uniformly_continuous_on f [a, b].
```

- Integration properties (file: `Lib/Integral.v`)

```coq
(* Additivity of the integral at an interior point c *)
Lemma integral_plus : forall f a b c,
  a < c < b -> integrable_on a b f -> ∫ a b f = ∫ a c f + ∫ c b f.

(* Additivity without ordering assumptions using min/max envelope *)
Lemma integral_plus' : forall f a b c,
  integrable_on (Rmin a (Rmin b c)) (Rmax a (Rmax b c)) f -> ∫ a b f = ∫ a c f + ∫ c b f.

(* Integral bounds from function bounds *)
Theorem theorem_13_7 : ∀ a b f m M,
  a <= b -> integrable_on a b f -> (∀ x, x ∈ [a, b] -> m <= f x <= M) ->
    m * (b - a) <= ∫ a b f <= M * (b - a).
```

- Trigonometry via integral definitions (file: `Lib/Trigonometry.v`)

```coq
(* π defined by area of a semicircle *)
Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

(* For each x in [0, π], a cosine value y in [-1,1] with A y = x/2 exists *)
Theorem cos_existence : forall x,
  0 <= x <= π -> { y | y ∈ [-1, 1] /\ A y = x / 2 }.
```

## Notation used throughout

Defined in `Lib/Notations.v`, `Lib/Limit.v`, and `Lib/Derivative.v`:

- Number types: `ℕ` = `nat`, `ℤ` = `Z`, `ℚ` = `Q`, `ℝ` = `R`
- Absolute value and square root: `|x|` = `Rabs x`, `√x` = `sqrt x`
- Interval predicates (open/closed): `[a,b]`, `[a,b⦆`, `⦅a,b]`, `⦅a,b⦆`, along with rays like `⦅-∞,b⦆`, `[a,+∞⦆` (used as sets on which functions are continuous/differentiable)
- Limits: `⟦ lim a ⟧ f = L`, `⟦ lim a⁺ ⟧ f = L`, `⟦ lim a⁻ ⟧ f = L`, plus ±∞ variants
- Derivatives: `⟦ der ⟧ f [a,b] = f'` for derivative on a closed interval, `⟦ der x ⟧ f = f'` for derivative at a point, and sided variants `⟦ der x⁺ ⟧`, `⟦ der x⁻ ⟧`
- Integrals: `∫ a b f` for the definite integral from `a` to `b`

## Repository structure

- `Lib/`: Core theory (limits, continuity, derivatives, integrals, sequences/series, completeness, sets, polynomials, etc.). Reusable across problem sets.
- `Calculus/`: Chapter- and problem-indexed files with worked formal proofs from the Calculus text.
- `ATTAM/`: Companion chapters depending only on `Lib/`.
- `_CoqProject`: Coq project configuration (logical roots and file list).

## How to build and explore

No Makefile assumed. You can compile any file directly with `coqc` (Coq must be installed):

```bash
coqc -Q Lib Lib -Q Calculus Calculus -Q ATTAM ATTAM Lib/Notations.v
coqc -Q Lib Lib -Q Calculus Calculus -Q ATTAM ATTAM Lib/Completeness.v
coqc -Q Lib Lib -Q Calculus Calculus -Q ATTAM ATTAM Lib/Continuity.v
coqc -Q Lib Lib -Q Calculus Calculus -Q ATTAM ATTAM Lib/Derivative.v
coqc -Q Lib Lib -Q Calculus Calculus -Q ATTAM ATTAM Lib/Integral.v
```

Or load the project in CoqIDE/VS Code with the `_CoqProject` file so qualified paths (Lib/…, Calculus/…) resolve automatically.

### Optional: generate a Makefile with coq_makefile

If you prefer `make`, you can generate a Makefile from `_CoqProject` using `coq_makefile` (part of Coq’s tooling):

```bash
# From the repo root
coq_makefile -f _CoqProject -o Makefile

# Build everything listed in _CoqProject
make -j

# Clean build artifacts
make clean
```

If `coq_makefile` is not found, install the `coq` package from your OS or opam, or ensure it’s on your PATH.

## Contributing

Issues and PRs are welcome — particularly for adding proofs to `Admitted` lemmas, new exercises in `Calculus/`, and additional automation/tactics.

## License

Add your preferred license (e.g., MIT/Apache-2.0) in a `LICENSE` file.
