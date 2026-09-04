# Formalization scope

## Status

The first project capstone is the combinatorial theorem below.  It is proved
in Lean, with the exact cardinality clause of Kopparty's Theorem 4.3 isolated
as the sole project-specific external input.

The second capstone is also proved.  It constructs the decoder from the paper,
proves that its output is exactly the decoding list, and bounds its running
time in a finite-field-operation model.  Kopparty's algorithmic clause in
Theorem 4.3 is the sole external *algorithmic* input.  Constructing and solving
the interpolation system, representing the interpolant, and filtering the
root-solver output are internal, checked parts of the development.

Two strengthened capstones are also proved.  They remove the manuscript's
choice `d = ceil(ε^(-3/θ))` and instead choose the derivative order freely.
For every fixed positive agreement and slack, the final rank comparison holds
for all sufficiently large `d`.  This extends the checked combinatorial and
algorithmic conclusions from the paper's sufficiently-low-rate regime to
every fixed rate strictly below the agreement fraction.

The manuscript snapshot used to choose the target is `Final.tex` with SHA-256

```text
f58c0ee49c6678076e8d6f012f0d98e25ef0f0485b08d219b706f3ed61bf9f9c
```

captured on 2026-09-02 (America/Los_Angeles), after reconciling the manuscript
with the checked repairs MF-001 through MF-014. The bibliography file
`main.bib` referenced by that snapshot is not present and must be restored
before the paper itself is reproducibly buildable.

## Exact capstone

For real parameters `θ` and `ε` and block length `n`, set

\[
\begin{aligned}
d&=\left\lceil\varepsilon^{-3/\theta}\right\rceil,&
m&=d^3,\\
A&=\lceil\varepsilon n\rceil,&
K&=\left\lfloor(1-\theta)\varepsilon n\right\rfloor,\\
B&=\left\lceil\frac{mA}{K-1}\right\rceil.
\end{aligned}
\]

The formalization target is the following proposition.

> For every `θ` with `0 < θ < 1`, there exists `ε₀ = ε₀(θ)` with
> `0 < ε₀ ≤ 1` such that the following holds for every `0 < ε < ε₀`.
> Let `n ≥ 1` and assume `d < K`. For every `1 ≤ k ≤ K`, every prime
> `q` satisfying
>
> \[
> n\le q,\qquad B<q,\qquad mA\le q^2,
> \]
>
> every injective evaluation map
> `α : Fin n → 𝔽_q`, and every received word `y : Fin n → 𝔽_q`,
>
> \[
> \left|\left\{p\in\mathbb F_q^k:
> \#\left\{i:\sum_{j=0}^{k-1}p_j\alpha_i^j=y_i\right\}\ge A
> \right\}\right|
> \le q^{4d+6}.
> \]

The chosen `ε₀` is also required to lie below the manuscript's displayed
small-epsilon threshold

\[
\left(\frac{\theta^3(1-\theta)}{768}\right)^{(5+\theta)/(1-\theta)}.
\]

This last upper bound keeps the target connected to the displayed parameter
calculation while allowing `ε₀` to absorb the manuscript's currently implicit
"sufficiently large `d`" requirements.

The Lean encoding is `RSListDecoding.CombinatorialMainStatement` in
`RSListDecoding/Statements.lean`. It uses `ZMod q` for `𝔽_q` and coefficient
vectors `Fin k → ZMod q` for degree-`< k` polynomials. Agreement at least
`A = ceil(εn)` is exactly the integer form of relative Hamming distance at
most `1-ε`.

## Strengthened all-rate capstone

Fix arbitrary `0 < ε < 1` and `0 < θ < 1`, and retain

\[
A=\lceil\varepsilon n\rceil,\qquad
K=\lfloor(1-\theta)\varepsilon n\rfloor.
\]

The strengthened theorem provides `d₀ = d₀(ε,θ)` such that every natural
`d ≥ d₀` works, provided `d < K`.  Set

\[
m=d^3,\qquad
B=\left\lceil\frac{mA}{K-1}\right\rceil.
\]

Then, under the direct field hypotheses

\[
n\le q,\qquad B<q,\qquad mA\le q^2,
\]

the same conclusions hold for every `1 ≤ k ≤ K`: the decoding list has size
at most `q^(4d+6)`, and the checked decoder returns it exactly in at most
`q^(C(d^4+1))` finite-field operations.  The corresponding Lean propositions
are `AllRateCombinatorialMainStatement` and
`AllRateAlgorithmicMainStatement`; the trusted-surface theorems are
`all_rate_combinatorial_main` and `all_rate_algorithmic_main`.

The new argument changes only the final parameter assembly.  The repaired
shell estimate already holds eventually in an independent `d`, and

\[
\frac{\theta^3}{262144}\frac{K-1}{n}
d^{2\theta/(5+\theta)}>1
\]

also holds eventually because `(K-1)/n` is bounded below by
`(1-θ)ε/2` and the exponent `2θ/(5+θ)` is positive.  All interpolation,
contact, multiplicity-root, root-counting, and filtering lemmas are reused.

Equivalently, for a target rate `R` and agreement `ε > R`, choose any
`θ` with `R ≤ (1-θ)ε`.  The theorem then decodes a rate-`R` code from an
error fraction approaching `1-R`, for fixed positive capacity gap.  The
existential shell threshold and the deliberately coarse factor `262144` make
the resulting constants potentially enormous; this is a qualitative
all-rate extension, not a practical parameter recommendation.

## Why the ambient dimension is `K`

The manuscript's interpolation dimension count needs a degree parameter near
`(1-θ)εn`, but the draft main theorem permits every smaller `k`. The scope
therefore performs interpolation and root counting at

\[
K=\lfloor(1-\theta)\varepsilon n\rfloor
\]

and obtains every `k ≤ K` by monotonicity under passage to a Reed--Solomon
subcode. This makes the intended low-rate assertion precise without silently
replacing an arbitrary `k` by `K`.

## Exact list bound

The public capstone uses `q^(4d+6)`, not big-O notation. Internally, the
root-counting step first establishes the sharper bound

\[
B(d+1)q^{4d+4}.
\]

This is the specialization of the cardinality clause of Kopparty's
[Theorem 4.3](https://theoryofcomputing.org/articles/v011a005/v011a005.pdf)
with root order `d`, degree cap `K-1 < q`, and parameter `B`. The direct
hypotheses `B < q` and `mA ≤ q²` are retained in the capstone instead of the
draft's conflicting constant-factor field estimates.

## Algorithmic extension

The algorithmic theorem uses the same rounded parameters and hypotheses as
the exact capstone.  On input the evaluation points and received word, the
decoder:

1. builds the homogeneous interpolation constraints on the canonical finite
   monomial basis;
2. computes a nonzero kernel vector by a checked finite-field linear-system
   algorithm;
3. converts that vector to the nonzero differential polynomial `Q`;
4. invokes Kopparty's Theorem 4.3 algorithm to enumerate all degree-`< K`
   polynomial solutions of the differential equation; and
5. retains exactly the degree-`< k` solutions with at least `A` agreements.

The cost is the number of finite-field additions, subtractions, negations,
multiplications, inversions, and equality tests.  Each such operation costs
one.  Index manipulation, natural-number arithmetic, allocation, and control
flow are not charged.  Thus the theorem is an algebraic-operation bound, not
a bit-complexity claim.  The public proposition asserts one absolute constant
and, at each admissible parameter choice, one decoder uniform in the received
word.  Its checked bound has the form

\[
q^{C(d^4+1)}=q^{O(\varepsilon^{-12/\theta})}
\]

where the witness is
`C = kopparty_theorem_4_3_algorithm.exponentConstant + 34`.  Internally, the
constructed decoder satisfies the stronger `q^(C(d+1))` bound; the fourth
power is retained in the public statement to match the manuscript's
conservative runtime.  The externally supplied `q^{O(r+rD/q+1)}` clause is
represented by a single uniform constant, rather than treating big-O notation
as executable data.

The exact Lean proposition is
`RSListDecoding.AlgorithmicMainStatement` in
`RSListDecoding/Statements.lean`; its proof is delegated by
`RSListDecoding.algorithmic_main`.

## In scope

- The exact finite-field and Reed--Solomon definitions used in the capstone.
- The hidden-derivative interpolation argument needed for the cardinality
  bound.
- The required lattice/counting, rank, degree, and parameter inequalities.
- A precisely cited combinatorial root-counting input, either formalized or
  isolated in `RSListDecoding/Assumptions.lean`.
- The sharper internal bound and the clean public bound above.
- The subcode argument from ambient dimension `K` to every `k ≤ K`.
- The cost annotations above and a checked finite-field linear-system solver.
- An explicit interpolation constraint matrix and its conversion to `Q`.
- Decoder soundness and completeness, including the final degree/agreement
  filter.
- The finite-field-operation bound for interpolation, root finding, and
  filtering.
- The algorithmic clause of Kopparty's Theorem 4.3, isolated with exact
  provenance as the sole external algorithmic input.

## Out of scope

- Bit complexity, machine-word complexity, memory use, or wall-clock time.
- Formal verification of Kopparty's root-finding implementation; its complete
  output and finite-field-operation bound are the one external algorithmic
  input.
- Computational certificates; none are presently needed for this target.
- A fully explicit closed formula for `ε₀(θ)` until all hidden threshold
  conditions in the draft have been made explicit.
- Practical bounds for the new threshold `d₀(ε,θ)`; the shell component is
  presently existential and the checked rank comparison intentionally keeps
  coarse discrete losses.

## Manuscript normalization implemented by this scope

The checked manuscript now uses these choices:

1. Use ambient `K` in the interpolation argument and derive smaller `k` by
   subcode monotonicity.
2. Reconcile the local-rank lemma's displayed exponent with the negative
   exponent used by the interpolation dimension comparison.
3. Reconcile the two shell-growth exponents and make the large-`d` threshold
   explicit; the existential `ε₀(θ)` currently absorbs it.
4. Resolve the ceiling/floor mismatch in the definition and use of
   `mathcal G`.
5. Replace the inconsistent field constants in the main theorem discussion
   by proved consequences of the direct conditions `B < q` and `mA ≤ q²`.
6. Replace the conflicting big-O list exponents by the exact public bound
   `q^(4d+6)`.

## Trust boundary

Only results genuinely imported from literature or external computation may
be declared in `RSListDecoding/Assumptions.lean`. Difficult steps belonging
to this paper remain proof obligations. Every external declaration must name
its source and paper role. The build and CI reject proof holes and reject
trust-extending declarations outside that file.

There are exactly two project-specific declarations there: the cardinality and
algorithmic clauses of the same Kopparty theorem.  The algorithmic clause is
the only external algorithmic declaration.
