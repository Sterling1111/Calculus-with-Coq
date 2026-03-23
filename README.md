# spivak-rocq

A formal, textbook-style development of single-variable calculus and supporting real analysis in the Coq proof assistant. While the project uses the standard library `Reals` type as its foundation for the real numbers, **all other calculus infrastructure (limits, continuity, derivatives, integrals, sequences, and transcendental functions) is built completely independently from scratch**. This formalization strictly follows the presentation and problem sequence of Michael Spivak’s "Calculus". The repository includes a reusable library (`Lib/`) plus worked problems for the Calculus track (`Calculus/`) and companion materials (`ATTAM/`).

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
Theorem rolles_theorem : ∀ f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f (a, b) -> f a = f b -> ∃ x, critical_point f (a, b) x.

Theorem mean_value_theorem : ∀ f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f (a, b) -> ∃ x, x ∈ (a, b) /\ ⟦ der x ⟧ f = (λ _, (f b - f a) / (b - a)).

Theorem cauchy_mvt : ∀ f f' g g' a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' -> 
    (∀ x, x ∈ (a, b) -> g' x <> 0) -> g b <> g a -> ∃ x, x ∈ (a, b) /\ (f b - f a) / (g b - g a) = f' x / g' x.
```

- Completeness (Least Upper/Greatest Lower Bounds) toolkit (file: `Lib/Completeness.v`)

```coq
Lemma completeness_upper_bound : ∀ E:Ensemble ℝ,
  has_upper_bound E -> E ≠ ∅ -> { sup | is_lub E sup }.

Lemma completeness_lower_bound :
    ∀ E:Ensemble ℝ, has_lower_bound E -> E ≠ ∅ -> { inf | is_glb E inf }.

Lemma lub_unique : ∀ (E:Ensemble ℝ) a b, is_lub E a -> is_lub E b -> a = b.

Lemma glb_unique : ∀ (E:Ensemble ℝ) a b, is_glb E a -> is_glb E b -> a = b.
```

Additional substantial developments include limits and continuity laws (`Lib/Limit.v`, `Lib/Continuity.v`), derivatives and rules (`Lib/Derivative.v`), series and sequences (`Lib/Series.v`, `Lib/Sequence.v`), and a Riemann-style integral with partitions (`Lib/Integral.v`). The trigonometry module derives classical results from integral definitions.

### More notable lemmas and theorems

- Algebra/Combinatorics (file: `Lib/Binomial.v`)

```coq
Theorem Binomial_Theorem_R : ∀ a b n,
  (a + b) ^ n = sum_f 0 n (λ i, (choose n i) * a ^ (n - i) * b ^ i).
```

- Differentiation rules (file: `Lib/Derivative.v`)

```coq
Theorem derivative_pow : ∀ n,
  ⟦ der ⟧ (λ x, x^n) = (λ x, INR n * x ^ (n - 1)).

Theorem derivative_mult : ∀ f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.

Theorem derivative_div : ∀ f f' g g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> (∀ x, g x <> 0) ->
  ⟦ der ⟧ (f / g) = (g ∙ f' - f ∙ g')%function / (g ∙ g).

Theorem derivative_comp : ∀ f g f' g',
  ⟦ der ⟧ g = g' -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ (f ∘ g) = ((f' ∘ g) ∙ g').
```

- Intermediate Value forms and consequences (file: `Lib/Continuity.v`)

```coq
Theorem intermediate_value_theorem_zero : ∀ f a b,
  a < b -> continuous_on f [a, b] -> f a < 0 < f b -> { x | x ∈ [a, b] /\ f x = 0 }.

Theorem intermediate_value_theorem : ∀ f a b c,
  a < b -> continuous_on f [a, b] -> f a < c < f b -> { x | x ∈ [a, b] /\ f x = c }.

Theorem intermediate_value_theorem_decreasing : ∀ f a b c,
  a < b -> continuous_on f [a, b] -> f b < c < f a -> { x | x ∈ [a, b] /\ f x = c }.
```

- Extreme value and bounds on closed intervals (file: `Lib/Continuity.v`)

```coq
Theorem continuous_on_interval_attains_maximum : ∀ f a b,
  a < b -> continuous_on f [a, b] -> ∃ x1, x1 ∈ [a, b] /\ (∀ x2, x2 ∈ [a, b] -> f x1 >= f x2).

Theorem continuous_on_interval_attains_minimum : ∀ f a b,
  a < b -> continuous_on f [a, b] -> ∃ x1, x1 ∈ [a, b] /\ (∀ x2, x2 ∈ [a, b] -> f x1 <= f x2).
```

- Uniform continuity on compact intervals (file: `Lib/Continuity.v`)

```coq
Theorem continuous_on_imp_uniformly_continuous_on : ∀ f a b,
  a <= b -> continuous_on f [a, b] -> uniformly_continuous_on f [a, b].
```

- Integration properties (file: `Lib/Integral.v`)

```coq
Lemma integral_plus : ∀ f a b c,
  a < c < b -> integrable_on a b f -> ∫ a b f = ∫ a c f + ∫ c b f.

Lemma integral_plus' : ∀ f a b c,
  integrable_on (Rmin a (Rmin b c)) (Rmax a (Rmax b c)) f -> ∫ a b f = ∫ a c f + ∫ c b f.

Theorem theorem_13_7 : ∀ a b f m M,
  a <= b -> integrable_on a b f -> (∀ x, x ∈ [a, b] -> m <= f x <= M) ->
    m * (b - a) <= ∫ a b f <= M * (b - a).
```

- Taylor's Theorem, transcendental bounds, and irrationality (files: `Lib/Taylor.v`, `Lib/PI_irrational.v`)

```coq
Theorem Taylors_Theorem : ∀ n a x f,
  a < x -> (∃ δ, δ > 0 /\ nth_differentiable_on (S n) f (a - δ, x + δ)) ->
    ∃ t, t ∈ (a, x) /\ f x = P(n, a, f) x + R(n, t, f) x.

Theorem π_bounds : 3.141591 < π < 3.141596.

Lemma e_bounds : 2.7182 < e < 2.7183.

Theorem theorem_16_1 : π ∉ ℚ.
```

- Trigonometry features a robust analytic definition based on inverses of integrals (file: `Lib/Trigonometry.v`). This has been expanded considerably; for instance, bounds on trig extensions and constants are now verified.

```coq
Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

Lemma pythagorean_identity : ∀ x, (sin x)^2 + (cos x)^2 = 1.

Lemma derivative_sin : ⟦ der ⟧ sin = cos.

Lemma derivative_cos : ⟦ der ⟧ cos = -sin.
```

## Standard Library Compatibility (`Lib/Compat.v`)

An extensive compatibility layer bridges the custom definitions in this repository directly to Coq's standard library `Reals`. This makes it possible to seamlessly interoperate between this project's foundational calculus theorems and external Coq developments:
- **Core Calculus**: Equivalences for limits, continuity, derivatives, and the Fundamental Theorem of Calculus.
- **Transcendental Functions**: Custom definitions for trigonometric functions, `exp`, `log`, as well as constants `PI` and `e` are formally proven equivalent to their `Reals` counterparts.

## Custom Automation

To efficiently discharge complex differential, continuity, and limit goals without manually applying properties like the chain rule or product rule, this project provides a robust custom tactical suite: `auto_diff`, `auto_cont`, and `auto_limit`. These heavily optimize evaluation and avoid the overhead of manually decomposing layered compositions.

For example, `auto_diff` can instantly solve deeply nested derivative problems (e.g. from Spivak's Chapter 10, Problem 1) purely through automation:

```coq
Lemma lemma_10_1_viii : ⟦ der ⟧ (λ x, sin (cos (sin x))) = (λ x, cos (cos (sin x)) * (- sin (sin x) * cos x)).
Proof. auto_diff. Qed.
```

Similarly, `auto_limit` can automatically evaluate limits of complicated expressions (e.g. from Chapter 5, Problem 1) and `auto_cont` can effortlessly prove continuity over intervals (e.g. from Chapter 11, Problem 1):

```coq
Lemma lemma_5_1_iii : ⟦ lim 3 ⟧ (λ x, (x^3 - 8) / (x - 2)) = 19.
Proof. auto_limit. Qed.

Lemma example_cont : continuous_on (λ x, x^5 + x + 1) [-1, 1].
Proof. auto_cont. Qed.
```


## Repository structure

- `Lib/`: Core theory (limits, continuity, derivatives, integrals, sequences/series, completeness, sets, polynomials, etc.). Reusable across problem sets.
- `Calculus/`: Chapter- and problem-indexed files with worked formal proofs from the Calculus text. Currently features nearly 300 stated problems spanning Chapters 1 through 13, with **105 problems fully verified** (zero admitted lemmas).

  ### Chapter-by-Chapter Progress
  
  | Chapter | Progress | Completed |
  | :--- | :--- | :--- |
  | `Chapter  1` | <img src="https://placehold.co/184x12/28a745/28a745.png" width="184" height="12" alt=""/><img src="https://placehold.co/16x12/eeeeee/eeeeee.png" width="16" height="12" alt=""/> | `24/26` |
  | `Chapter  2` | <img src="https://placehold.co/179x12/28a745/28a745.png" width="179" height="12" alt=""/><img src="https://placehold.co/21x12/eeeeee/eeeeee.png" width="21" height="12" alt=""/> | `26/29` |
  | `Chapter  3` | <img src="https://placehold.co/11x12/28a745/28a745.png" width="11" height="12" alt=""/><img src="https://placehold.co/189x12/eeeeee/eeeeee.png" width="189" height="12" alt=""/> | ` 1/17` |
  | `Chapter  5` | <img src="https://placehold.co/61x12/28a745/28a745.png" width="61" height="12" alt=""/><img src="https://placehold.co/139x12/eeeeee/eeeeee.png" width="139" height="12" alt=""/> | `13/42` |
  | `Chapter  6` | <img src="https://placehold.co/94x12/28a745/28a745.png" width="94" height="12" alt=""/><img src="https://placehold.co/106x12/eeeeee/eeeeee.png" width="106" height="12" alt=""/> | ` 8/17` |
  | `Chapter  7` | <img src="https://placehold.co/47x12/28a745/28a745.png" width="47" height="12" alt=""/><img src="https://placehold.co/153x12/eeeeee/eeeeee.png" width="153" height="12" alt=""/> | ` 4/17` |
  | `Chapter  8` | <img src="https://placehold.co/10x12/28a745/28a745.png" width="10" height="12" alt=""/><img src="https://placehold.co/190x12/eeeeee/eeeeee.png" width="190" height="12" alt=""/> | ` 1/20` |
  | `Chapter  9` | <img src="https://placehold.co/64x12/28a745/28a745.png" width="64" height="12" alt=""/><img src="https://placehold.co/136x12/eeeeee/eeeeee.png" width="136" height="12" alt=""/> | `10/31` |
  | `Chapter 10` | <img src="https://placehold.co/33x12/28a745/28a745.png" width="33" height="12" alt=""/><img src="https://placehold.co/167x12/eeeeee/eeeeee.png" width="167" height="12" alt=""/> | ` 6/36` |
  | `Chapter 11` | <img src="https://placehold.co/53x12/28a745/28a745.png" width="53" height="12" alt=""/><img src="https://placehold.co/147x12/eeeeee/eeeeee.png" width="147" height="12" alt=""/> | `11/41` |
  | `Chapter 12` | <img src="https://placehold.co/200x12/eeeeee/eeeeee.png" width="200" height="12" alt=""/> | ` 0/14` |
  | `Chapter 13` | <img src="https://placehold.co/8x12/28a745/28a745.png" width="8" height="12" alt=""/><img src="https://placehold.co/192x12/eeeeee/eeeeee.png" width="192" height="12" alt=""/> | ` 1/24` |

- `ATTAM/`: Companion chapters depending only on `Lib/`.
- `_CoqProject`: Coq project configuration (logical roots and file list).

## How to build and explore

This project is built and verified using **The Rocq Prover, version 9.1.1** (formerly Coq). 

### Prerequisites

The project will compile successfully even if the C++ simplex program is not built. However, the custom `psatz` tactic for real linear arithmetic will not work without it. Note that this tactic was merely an experiment to implement the ideas from the paper *Fast Reflexive Tactics* and should generally not be used anyway (rely on `lia` or `lra` instead). If you still wish to compile it:

```bash
# From the repo root
g++ -O3 simplex.cpp -o simplex_solver
```

### Compiling the Project

The recommended way to build the project is by generating a `Makefile` from the `_CoqProject` file using `coq_makefile` (part of Rocq/Coq's standard tooling) and then running `make`.

```bash
# Generate the Makefile
coq_makefile -f _CoqProject -o Makefile

# Build everything listed in _CoqProject concurrently
make -j

# Clean build artifacts
make clean
```

If `coq_makefile` is not found, install the `coq` package from your OS or opam, or ensure it is on your PATH.

Alternatively, you can load the project in CoqIDE/VS Code with the `_CoqProject` file so qualified paths (`Lib/…`, `Calculus/…`) resolve automatically.

## Contributing

Issues and PRs are welcome — particularly for adding proofs to `Admitted` lemmas, new exercises in `Calculus/`, and additional automation/tactics.

## License

This project is released under the MIT License. See the `LICENSE` file for details.
