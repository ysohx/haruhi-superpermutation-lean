# A verified lower bound for fourteen-symbol superpermutations

**Lean-checked result (9 October 2026): every superpermutation on fourteen symbols has length at least 93,890,701,078.** Literature novelty and publication priority have not been established. This project has not been externally peer reviewed.

## Authorship

**OpenAI Codex developed this extension and generated its new argument, Lean proof code, computational checks, and documentation, including work by parallel Codex agents.** The human participant proposed the investigation and guided the conversation; the proof is not presented as human-written.

This builds on the prior research and formalizations credited below. It is not an official OpenAI publication. See [AUTHORSHIP.md](AUTHORSHIP.md) for the division of work and review provenance.

The final theorem in `Haruhi/Main.lean` is:

```lean
theorem superpermutation_fourteen_lower_bound
    (w : List ℕ) (hw : Hunter.IsSuperperm 14 w) :
    93890701078 ≤ w.length
```

`Hunter.IsSuperperm 14 w` means that every permutation of the symbols 1 through 14 occurs as a **contiguous subword** of `w`. The final theorem has no hypothesis about residuals, component capacities, or reduced Hamiltonian paths. A second theorem proves `93890701078 ≤ Hunter.Ssuper 14`, the actual minimum length.

## Proof overview

The main idea is to show that the cheapest local arrangements cannot all fit together in a single global solution. The proof makes this precise by bounding how many permutations can be covered for a given amount of extra length.

**1. Turn overlaps into a weighted path.** Regard each of the $14!$ episode orders as a vertex. An edge records the minimum number of symbols that must be appended to move from one order to the next, using their suffix–prefix overlap. A Hamiltonian path visits every order exactly once; its weight $W$ gives a word length of $W+14$. The existing formalized word-to-graph bridge and reduction theorem let us prove the bound for reduced Hamiltonian paths first. The reduction never increases weight, so a lower bound for those paths also applies to arbitrary superpermutation words.

**2. Group permutations into rotation classes.** The fourteen cyclic rotations of an order form one class, giving $14!/14=13!$ classes in total. Hunter's transformation organizes these classes into components. Within a component, consecutive classes connected by weight-two edges form an *interval piece*, containing at most thirteen classes. A piece with thirteen classes is *full*; its *deficit* is thirteen minus its size. For the local analysis, the construction prepends one auxiliary rotation class to each component except one distinguished root. If there are $h$ components, their augmented class counts therefore sum to $13!+h-1$. These auxiliary copies are accounted for explicitly.

**3. Prove that nearly full pieces have unavoidable losses.** A key local obstruction rules out a full thirteen-class piece followed by two twelve-class pieces when both connecting edges have weight three. The possible transitions would force a rotation class to be visited twice, contradicting the path's distinctness. Combining this obstruction with the existing interval-piece theory bounds the size of every actual augmented component:

$$
9b_i \le 1577r_i + 1404(\eta_i+1).
$$

Here $b_i$ is its number of rotation classes, $\eta_i$ is the total excess of its inter-piece edge weights above three, and $r_i$ is a corrected nonnegative accounting quantity built from piece deficits, piece counts, and endpoint and edge corrections. It is not a count of missing episodes. The proof establishes both $r_i\ge0$ and the capacity inequality from the constructed paths.

**4. Control components that appear to cost nothing.** The local bound still gives each component an allowance even when its accounting quantities vanish, so it is essential to control the number of components. A *standard* component has a newly created head whose selected outgoing edge in the original path has weight two, together with zero residual and heavy-seam excess. Its augmented path is forced into a rigid shape: twelve interval pieces, total deficit one, and 155 rotation classes. The endpoint analysis proves that two standard components cannot be linked through a direct transformation slot (the connection used in the component-counting argument). An injective counting argument then bounds the number of standard components by the number of nonstandard components plus explicitly charged exceptions. This prevents arbitrarily many locally cheap components from evading the global bound.

**5. Sum the exact accounting identities.** For a reduced Hamiltonian path, define its excess $\delta$ by

$$
W+14 = \underbrace{14!+13!+12!+11}_{93,884,313,611}+\delta,
\qquad T=77\delta-12!+12.
$$

The proof expresses $T$ exactly as a sum of nonnegative residual and exception charges. Combining that identity with the component count and local capacities, and subtracting the $h-1$ auxiliary classes, yields

$$
9\cdot13! \le 4367T+2799
       =4367(77\delta-12!+12)+2799.
$$

The constants include the endpoint and augmentation corrections; no capacity or matching assumption remains in the final theorem.

**6. Round in the integers and return to words.** With $13!=6,227,020,800$ and $12!=479,001,600$, the last inequality forces $T\ge12,833,338$ and then $\delta\ge6,387,467$. Consequently,

$$
W+14\ge93,884,313,611+6,387,467
      =\boxed{93,890,701,078}.
$$

The reduction and word-to-graph bridge transfer this bound to every fourteen-symbol superpermutation, and hence to the minimum possible length. This establishes a lower bound; it does not construct a word of that length or determine the exact minimum. The source-file map below identifies where each part is formalized.

## Verification

Toolchain: **Lean 4.31.0**. All dependency revisions are pinned in `lakefile.toml` and `lake-manifest.json`.

With that toolchain installed and `lean`/`lake` on PATH:

```sh
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

Keep the shipped `lake-manifest.json` unchanged to reproduce the locked dependency versions. The cache command downloads compiled mathlib dependencies; our proof is built from the included source files. The final axiom audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard classical foundations. The final theorem does not depend on `sorryAx`, custom axioms, or `native_decide`. The project's own source contains no `sorry` or `admit`. Recorded build and audit output is in `verification/`; `manifest.json` identifies the exact delivered source files.

## Proof structure

1. `LocalGeometry`, `GapBridge`, and `ComponentCapacity` prove the local obstruction and refined capacity for actual paths.
2. `Augmentation` and `ActualAugmentation` construct the actual augmented Hunter components.
3. `Terminal`, `AugmentedTerminal`, `ZeroRigidity`, and `FirstSeam` prove that two standard components cannot connect through a direct cheap slot.
4. `GraphAccounting`, `HeadData`, `ActualCapacity`, `HeadCount`, `StandardMatching`, and `GlobalCapacity` establish exact accounting and the global count.
5. `Arithmetic` supplies exact integer rounding; `Lifting` removes the reduced-path condition and connects the result to ordinary superpermutation words.
6. `Main` combines those proved results into the unconditional final theorem.

Some intermediate arithmetic lemmas deliberately accept explicit hypotheses. `Main` discharges those hypotheses using the actual graph constructions.

## Prior work and attribution

This extends existing formalizations; it does not recreate Lean, mathlib, or the earlier superpermutation theory from scratch.

- [Hunter–Raudvere formalization (Zach Hunter and Uku Raudvere)](https://github.com/urdvr/superpermutations-hunter/tree/d45222190031d162feb1f6f3cf5fe2d11fab726d), commit `d45222190031d162feb1f6f3cf5fe2d11fab726d`. Apache 2.0. `Augmentation.lean` adapts its `ProofsPu.pu_exists_with_verts`, retaining the original copyright notice and allowing any external predecessor.
- [Preimage-chain formalization (Xiaolong Liu)](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds/tree/8474c74a15fa59b8ce55bcf6bceaaa23b9a3dca8), commit `8474c74a15fa59b8ce55bcf6bceaaa23b9a3dca8`. CC BY 4.0. We reuse its proved graph, path, and interval-piece machinery. Coordinate and endpoint proof templates in `Terminal.lean` adapt that source; the new deficit-one, augmentation, and matching conclusions are proved here.
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f), commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Apache 2.0.
- [Kisic's draft](https://github.com/mkisic/superpermutations/blob/57ce244796c4c20ddbc708a5093828194c93ea9b/lower_bound_unverified.tex) informed the exploratory argument. Its unformalized results are **not assumed as axioms** in this Lean proof.

The bound is 166,667 above the 93,890,534,411 consequence of the pinned Kisic draft, and 444,637 above the 93,890,256,441 displayed preimage-chain corollary. Those comparisons concern these specific sources, not an exhaustive claim about the literature.

The new work was generated by Codex as detailed in [AUTHORSHIP.md](AUTHORSHIP.md). Acceptance rests on the compiled theorem and its meaning. Outside mathematical review is still welcome.
