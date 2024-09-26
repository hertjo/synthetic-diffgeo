# Synthetic Differential Geometry

This project implements core structures and algorithms of **Synthetic Differential Geometry (SDG)** in Agda. SDG is a reformulation of differential geometry where infinitesimals are treated as actual nilpotent quantities in a topos-theoretic or categorical framework. It replaces the traditional limit-based analysis with algebraic, logical, and geometric axioms. Below is a breakdown of the theoretical structures covered and implemented.

## Differential Cohesion and Infinitesimal Shape Modalities

### ISM: Infinitesimal Shape Modality

This part models the **Infinitesimal Shape Modality** $\int$ used in differential cohesion. Given a cohesive topos, the infinitesimal shape modality $\int$ reflects spaces to their infinitesimal cores — removing global topological information and preserving only infinitesimal data.

- For a space $X$, $\int X$ is the **formal neighborhood** of the diagonal $\Delta \subset X \times X$.
- This captures the idea of infinitesimal proximity: two points in $\int X$ are "infinitesimally close."

We define $\int$ as a **left-exact modality** satisfying:

$$
\int : \mathcal{E} \to \mathcal{E}, \quad \text{with unit } \eta_X : X \to \int X
$$

such that:

- $\int$ preserves finite limits,
- $\eta_X$ is a monomorphism,
- $\int X$ is infinitesimally contractible.

This enables modeling differential forms and tangent vectors intrinsically.

## Infinitesimals

We implement the ring of **infinitesimal elements** in the form of Weil algebras.

### Infinitesimal Line $D$

Defined as:

$$
D := \{ d \in R \mid d^2 = 0 \}
$$

In SDG, the tangent space at a point $p \in M$ is represented as:

$$
T_p M := \{ f : D \to M \mid f(0) = p \}
$$

This intrinsic definition replaces the limit-based definition of derivatives.

### Derivatives

Given $f : R \to R$, its derivative at $x$ is defined as the unique $f'(x)$ such that:

$$
f(x + d) = f(x) + f'(x) \cdot d \quad \text{for all } d \in D
$$

This relation is enforced algebraically in SDG.

## Kock–Lawvere Axiom

This axiom underpins SDG and is implemented as a foundational assumption:

**Kock–Lawvere Axiom:**

If $f : D \to R$ is a function, then there exists a unique $a \in R$ such that:

$$
f(d) = f(0) + a \cdot d \quad \text{for all } d \in D
$$

This ensures that all functions in SDG are **infinitesimally linear**, making every function automatically differentiable.

## Weil Algebras

Weil algebras generalize the notion of infinitesimals.

### Base

A **Weil algebra** $W$ is a finite-dimensional, local, commutative $R$-algebra with a unique maximal ideal $m$ such that:

$$
m^n = 0 \quad \text{for some } n \in \mathbb{N}
$$

Examples include:

- Dual numbers: $R[\epsilon]/(\epsilon^2)$
- Truncated polynomial rings: $R[\epsilon]/(\epsilon^n)$

### Functorial Interpretation

Each Weil algebra defines a functor:

$$
T_W(X) := \text{Hom}_{\text{Alg}}(\text{Spec}(W), X)
$$

which describes the infinitesimal thickening of a space $X$ via $W$.