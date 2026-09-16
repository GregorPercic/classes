# Formalized admissibility of classes

This is a formalization project for my master's thesis. Admissibility of classes tells us that adding class notation, meaning class variables and set builder notation, to first-order set theory is safe, in the sense explained below. Admissibility of classes consists of two theorems. Let CT be the theory of classes and ST the theory of sets (details about them can be found in `TTheory.agda` and `Theory.agda`).

**The Eliminability Theorem.** For every class formula Φ and a class variable substitution eliminating all class variables σ, there exists a set formula φ such that CT ⊢ Φ[σ] ⇔ φ.

```agda
existential-eliminability : ∀ {C Γ Hyp} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) →
  ∃[ φ ] Proof CT {𝟘} {Γ} Hyp (Subst-Formula σ Φ ⇔ inj-formula φ)
```

Intuitively, this theorem guarantees that any property expressible in the language of classes (without class variables) is also expressible in the language of sets.

**The Conservation Theorem.** For every set formula φ, CT ⊢ φ holds if and only if ST ⊢ φ holds.

```agda
conservation-corollary : ∀ {C Γ} (φ : formula Γ) →
  Proof CT {C} {Γ} [] (inj-formula φ) ↔ proof ST {Γ} [] φ
```

Intuitively, this theorem tells us that adding class notation does not let us prove more facts about sets. The set formulas provable in class theory are exactly those provable in set theory.

Some fundamental choices of the formalization, such as the choice to include class variables, the choice of axioms for CT and ST, and the formulations of both theorems, are based on the presentation in *Basic Set Theory* by Azriel Levy. Nevertheless, the proofs themselves are, to my knowledge, novel.

This formalization was motivated by a complaint made on the [Metamath Proof Explorer Home Page](https://us.metamath.org/mpeuni/mmset.html).

> But there is no simple way to verify automatically the soundness of our three class definitions. Instead, we must trust the relatively involved metamathematics of Levy's (or other authors') eliminability and conservation proofs that exist only on paper, at least until a sufficiently sophisticated definitional soundness checker becomes available.

I hope that this formalization meaningfully contributes to greater confidence in the soundness of Metamath's development of set theory, by moving these two crucial theorems from paper to silicon.

The formalization runs on Agda 2.8.0 with agda-stdlib 2.3.