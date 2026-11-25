# Verified results on Boolean circuit size

This collection contains results for the P vs NP project's circuit benchmarks. One identifies which circuit designs are still worth searching on one explicit graph. Another classifies the negative inputs of the Fano incidence benchmark. A third reduces an exact circuit lower-bound conjecture to an asymptotic bound on a more structured class of graphs. P versus NP remains open.

## An 11-input circuit must reuse a computed value to meet the target

On the project's 11-vertex graph, the answer is true when the selected vertices contain an edge. A monotone formula for this function needs exactly **23 input occurrences and 22 binary gates**. The project's ordinary circuit search targets 21 gates. This rules out every design in which each computed value is used at most once.

The lower bound uses the graph's 16 edges and 24 maximal independent sets. A formula leaf separates a rectangle of positive and negative input pairs. A formula with 22 leaves would partition all 384 pairs into at most 22 such rectangles. The evidence includes the formula-to-partition theorem, a checked translation of the rectangle constraints into a Boolean formula, and a certificate showing that those constraints have no solution. The Lean executable checks the translation and the certificate against the very same 17,476 clauses. The upper bound assigns each edge to one of seven stars. The replay tests its 23-leaf formula on all 2,048 possible inputs. [Formula theorem](g11/FormulaRectPartition.lean) · [Encoding theorem](g11/RectangleCNFBridge.lean) · [Certificate replay](g11/ReplayRectangleCNF.lean)

For project step L-meta-6796 we have a concrete circuit with 15 preparation gates and four pairs of outputs. The step charges two per pair, giving a total of **23** against the required **22**. Lean checks the actual gate evaluations, output pairs and structural requirements. The package includes the gate list so another researcher can modify it. The unrestricted 22-charge question is open. A separate theorem gives a rectangle bound for a circuit that exposes just one prepared wire to the remaining formula. [Circuit and proof](g11/CoverAt23.lean) · [Gate list](g11/charge-23.json) · [Single-wire theorem](g11/SingleSharedFormula.lean)

## Seven rotation classes cover the Fano benchmark's negative boundary

The Fano incidence graph has seven points and seven lines. An input that contains no incident point–line pair gives a negative answer. Its maximal negative inputs are the independent sets to which no other vertex can be added. Our Lean proof shows that there are **exactly 37**, and classifies them under simultaneous cyclic relabeling of the points and lines. The seven orbit sizes are **1, 7, 7, 7, 7, 7, 1**. This gives explicit negative test inputs for checking monotone circuit candidates.

Starting with any set of points, add every compatible line, then every point compatible with those lines. The proof shows that this completion is maximal, that it contains the original points, and that every maximal pair is a rotation of one of the seven listed masks. The project's coverage statement follows from this classification. The official local checker accepted this exact statement and rechecked 1,672 constants. Another contributor supplied the site's merged proof of the coverage statement. [Classification and Lean proof](fano/L_meta_11463.lean) · [Checker verdict](fano/checker.log) · [Merged project proof](https://github.com/open-goat/pequalnp-proofs/pull/15208)

## An asymptotic bound would settle an exact incidence conjecture

Project step L-meta-3491 concerns the minimum circuit size for detecting an edge in a bipartite graph that contains no cycle of length four. Our reduction shows that it suffices to prove a lower bound on symmetric square incidence tables with an involution matching every row to a column. The simpler-looking bound may have an additive error that is uniformly sublinear in the side length.

The construction combines a graph with a copy having its shores exchanged, then takes repeated disjoint copies. An exact shortfall of even one gate would grow linearly with the number of copies and eventually exceed the allowed error. The constructive part is proved in Lean. The asymptotic lower bound itself remains a hypothesis. The public pull request contains the exact reduction, and its intake comment records the checker's acceptance and the reason it was not recorded on the project desk. [Constructive normalization](incidence/AmplifiedNormalization.lean) · [Reduction](incidence/R_meta_3491_627.lean) · [Project intake decision](https://github.com/open-goat/pequalnp-proofs/pull/10073#issuecomment-7152998315)

## Reproduce the checks

Use Python 3 and the Lean toolchain pinned by the project. The recorded replay used revision `81b4fafd7a831eef210ad183d6864e5f167ec1d9` of the public repository. In a clone of that revision, build the dependencies once.

```sh
cd pequalnp-proofs/lean
lake exe cache get
lake build PEqualNP.Defs PEqualNP.MetaComplexity.Helpers.Elim PEqualNP.Outside.L_meta_3140
```

From this collection, pass the path of that checkout to the verifier.

```sh
python3 verify.py /path/to/pequalnp-proofs
```

The verifier checks file hashes, evaluates both G11 constructions on all inputs, compiles the Lean theorems, and replays the supplied certificate. The certificate replay is an executable Lean check of concrete data. The accompanying soundness theorems are kernel-checked. [Project revision](https://github.com/open-goat/pequalnp-proofs/tree/81b4fafd7a831eef210ad183d6864e5f167ec1d9)
