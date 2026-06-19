# Finite-State Transducers in Lean 4

[![CI](https://github.com/alexeyev/finite-state-transducers-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/alexeyev/finite-state-transducers-lean/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.30.0-blue.svg)](https://leanprover.github.io/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

A self-contained, machine-checked development of the core theory of **finite-state
transducers (FSTs)** and the **rational relations** they realize — formalized in
Lean 4 with **no dependency on Mathlib**.

Mathlib formalizes finite automata and regular *languages* (DFA / NFA / regular
expressions / Myhill–Nerode), but not transducers or rational *relations*. This
library fills that gap from first principles.

Every result is proved with **no `sorry` and no `admit`**. An axiom audit at the
end of the source (and surfaced on every `lake build`) shows that each result
depends only on Lean's standard logical axioms — `propext` and `Quot.sound` — and
in particular **never on `Classical.choice` or `sorryAx`**.

## Highlights

| Result | Lean name(s) |
| --- | --- |
| Closure under union, inverse, composition | `realizes_union`, `realizes_inv`, `realizes_compose` |
| Closure under concatenation and Kleene star | `realizes_concat`, `realizes_star` |
| Domain and range are recognizable | `accepts_dom`, `accepts_ran` |
| Restriction to a regular domain/range; image and preimage of a regular language are regular | `rational_restrict`, `diag`, `image_recognizable`, `preimage_recognizable` |
| Nivat / pair-alphabet characterization | `nivat` |
| **Kleene's theorem, forward**: every rational expression is realized | `RatExpr.denote_rational` |
| **Kleene's theorem, converse**: state elimination (Arden's lemma + generalized automata) | `arden_solution`, `arden_least`, `RPath_pivot_fwd/bwd`, `Rk_denotable`, `kleene_converse` |
| Converse, end to end: operational runs of a concrete finite transducer ⟹ rational expression | `pathN_iff_RPath`, `realizes_RPath`, `finTransducer_denotable`, `finTransducer_rational` |
| **Kleene's theorem, full structural form**: a relation is denotable iff realized by some finite transducer over `Fin n` | `FinEnc`, `FinPres`, `denote_finTransducer`, `kleene` |
| **Deterministic automata + Myhill–Nerode** (both directions): DFA ⟺ finite right-invariant, language-saturating coloring; DFA languages are regular | `DFA`, `dfa_coloring`, `dfa_of_coloring`, `dfa_accepts_iff` |
| **Boolean algebra of DFA languages**: closure under intersection, union, and complement (product / complement constructions) | `DFA.product`, `dfa_inter`, `dfa_union`, `DFA.compl`, `dfa_compl` |
| **Determinization (Rabin–Scott)**: subset construction `NFAe ⟹ DFA` with correctness; every regular language is DFA-recognizable | `NFAe.PathN.comp`, `NFAe.PathN.firstSymbol`, `NFAe.RX_cons`, `NFAe.det`, `NFAe.det_correct`, `NFAe.exists_dfa` |
| **Regular languages closed under complement** (determinize → negate acceptance → re-embed) | `nfae_compl_closed` |
| **Finiteness foundations** (toward a *finite* subset construction): loop removal shortens any ε-path to length ≤ N | `NFAe.PathN.epsStates`, `NFAe.eps_short` |
| **Decidable reachability** (with a decidable step relation): ε-closure computable as a `Bool`-valued set; reachability decidable for any word | `NFAe.decRX`, `NFAe.epsClosure`, `NFAe.RX_single_iff`, `NFAe.decRXsingle`, `NFAe.decRXword` |
| Sequential (input-deterministic) transducers compute partial functions | `inputDet_functional` |
| The **twinning property**, and that determinism implies it | `Twinning`, `inputDet_twinning` |
| The **subsequential transducer** model (deterministic, with initial + per-state final outputs — Choffrut's determinizable target): run semantics, and that it computes a partial function | `Subseq`, `Subseq.run`, `Subseq.realizes`, `Subseq.functional` |
| The **longest common prefix of a list of words**, and that it is a common prefix of every element — the soundness fact behind the determinization's emit step | `lcpList`, `lcpList_isPrefix`, `lcp_isPrefix_left`, `lcp_isPrefix_right` |
| **`lcpList` is the *greatest* common prefix** (with `lcpList_isPrefix`, exactly the longest); stripping it leaves residuals with no shared prefix, so the factored determinized states are **canonical** | `lcp_greatest`, `lcpList_greatest`, `lcpList_strip`, `detNext_lcpList_nil` |
| **Residual length is bounded by a pairwise prefix-distance:** in a canonical branch list, each word's residual length `≤ pdist` to some *other* branch — so a bound on pairwise `pdist` (bounded delay) bounds all residual lengths. The metric ingredient of finiteness | `lcp_cons_dichotomy`, `canon_diverge`, `residual_le_pdist` |
| The **determinization step** (residual subset construction) as a pure, computable operation on residual-states — raw successors, emit the longest common prefix, carry the remainders — and that the step loses no output | `rawSucc`, `detEmit`, `detNext`, `detStep_reconstruct` |
| The **determinized machine** assembled into a genuine (computable) `Subseq`, with the membership characterization of raw successors used for correctness | `detSubseq`, `mem_rawSucc_iff` |
| **Determinization correctness (run-level):** the total emitted output, prepended onto every residual of the final state, reconstructs the unfactored run — the construction loses no output, proved by induction via per-step reconstruction and prefix-equivariance | `rawRun`, `rawRun_prepend`, `rawSucc_eq_detNext_prepend`, `detRun_reconstruct` |
| **Determinization correctness (semantic):** a functional NFT and its determinization realize *exactly the same relation* — soundness needs no hypothesis, completeness uses functionality (the Choffrut hypothesis); packaged as an `↔` | `nftRel`, `detSubseq_sound`, `detSubseq_complete`, `detSubseq_correct` |
| The **determinized state space**: the reachable factored state after reading a word, shown equal to the run's state component and canonical on nonempty input — the setup for the finiteness argument | `detReach`, `detSubseq_run_state`, `detReach_snoc`, `detReach_canonical` |
| **Conditional finiteness:** under a δ-level bounded-delay bound `K` (exactly what twinning gives), every residual in a reachable determinized state has length `≤ K` — via the canonical form, the residual/`pdist` bound, and prefix-invariance of `pdist` | `pdist_prepend`, `dBoundedDelay`, `detReach_residual_bounded` |
| **Finitely many residuals:** over a finite output alphabet `Fin M`, all words of bounded length are enumerable (`wordsLE`), so every reachable residual is drawn from a finite set — the residual alphabet of the determinized machine is finite | `wordsExact`, `mem_wordsExact`, `wordsLE`, `mem_wordsLE`, `detReach_residuals_finite` |
| **Entries from a finite universe:** with finitely many NFT states (`Fin N`) and a finite output alphabet (`Fin M`), every entry of a reachable determinized state is a (state, residual) pair lying in the finite list `pairsLE N M K` — so each reachable state is a subset of one fixed finite set | `pairsLE`, `mem_pairsLE`, `detReach_pairs_finite` |
| **Finitely many states (up to set-equality):** a choice-free enumeration of all subsets of a list (`allSublists`, the `2^n` sublists); canonicalizing each reachable state against the universe lands it in `allSublists (pairsLE N M K)`, set-equal to the original — so the reachable states inject into an explicitly enumerated finite list | `allSublists`, `mem_allSublists_of_sublist`, `canonState`, `mem_canonState`, `canonState_mem_allSublists`, `detReach_canon_faithful`, `detReach_canon_mem_allSublists` |
| **Set-invariance of the step (bisimulation core):** the determinization step depends only on the *set* of (state, residual) entries, not order or multiplicity — `rawSucc`, the emitted `detEmit` (via `lcpList` being the greatest common prefix of the entry set), and `detNext` are all congruences for set-equality; the bridge from set-level finiteness toward a literal finite machine | `prefix_antisymm`, `lcpList_congr_mem`, `rawSucc_congr_mem`, `detEmit_congr`, `detNext_congr_mem` |
| **The canonical finite-state run:** `cstep` canonicalizes after each determinization step, so every state lies in `allSublists (pairsLE N M K)` (`cRun_mem_allSublists`); the run is well-defined up to set-equality, and computes the *same* reachable state as the raw determinization, set for set (`cRun_detReach`) — a literal finite-state realization of the state trajectory | `cstep`, `cRun`, `cstep_congr`, `cRun_congr_mem`, `cRun_detReach_mem`, `cRun_detReach`, `cstep_mem_allSublists`, `cRun_mem_allSublists` |
| **Explicit run output:** the determinized run returns exactly `(detReach, detOut)` — its state component is the reachable factored state, its output the concatenation of the per-step emits (strengthening the earlier existence-only statement) | `detOut`, `detSubseq_run_eq` |
| **Output-level bisimulation:** the canonical finite-state run's output (`cOut`) equals the raw determinized output (`detOut`) — same emits step-for-step, lossless canonicalization — so the determinized run's output *is* the finite machine's output (`detSubseq_run_canonical_output`); together with correctness, a functional NFT of bounded delay is realized by a finite subsequential machine at both state and output level | `cOut`, `cOut_congr`, `cOut_eq_detOut_mem`, `cOut_eq_detOut`, `detSubseq_run_canonical_output` |
| **Choffrut's theorem (bounded-variation form):** the capstone — a functional NFT whose branch outputs have bounded prefix-distance (`dBoundedDelay`) is realized by a finite subsequential transducer: it realizes the NFT relation, its run output is that of a finite-state canonical machine, and that machine's states lie in the finite `allSublists (pairsLE N M K)`. The `twinning ⇒ bounded-delay` step is bridged to the δ-model and isolated to a single `rawRun ↔ Reaches` correspondence | `choffrut_subsequential`, `dBoundedDelay_of_reaches`, `dBoundedDelay_of_twinning` |
| **Bridge closed for single-symbol NFTs (unconditional):** for NFTs whose transitions emit ≤ 1 letter, a real-time transducer (`nftT`) is extracted and the `rawRun ↔ Reaches` correspondence is *proved* (induction matching `rawSucc`-accumulation to `PathN`), discharging bounded variation from twinning outright — a twinning, functional, single-symbol NFT is realized by a finite subsequential transducer with **no** bounded-variation hypothesis | `olist_of_len_le_one`, `nftT`, `nftT_realtime`, `mem_rawRun_iff_path`, `mem_rawRun_iff_reaches`, `choffrut_subsequential_of_twinning` |
| **Deterministic case (word outputs, unconditional):** a deterministic NFT (`≤ 1` start state, `≤ 1` transition per state/letter) carries `≤ 1` reachable branch (`rawRun_length_le_one`), so bounded delay holds with constant `0` and functionality is automatic — a deterministic *word-output* NFT is realized by a finite subsequential transducer with **no** hypotheses at all | `eq_of_mem_length_le_one`, `rawSucc_length_le_one`, `rawRun_length_le_one`, `dBoundedDelay_of_deterministic`, `nftRel_functional_of_deterministic`, `choffrut_subsequential_deterministic` |
| **Concrete worked example:** a one-state word-output transducer (`0 ↦ 00`, `1 ↦ 1`) instantiates *both* unconditional routes — the deterministic theorem (`Example.dbl_choffrut`) and the word-output *twinning* theorem (`Example.dbl_choffrut_twinning`, with `DTwinning` from `dtwinning_of_deterministic`); the determinizer and the canonical finite machine both *compute* `[0,0,1,0,0,1]` on input `[0,1,0,1]` under `#eval` — the whole pipeline exercised on a real machine | `Example.dblδ`, `Example.dbl_choffrut`, `Example.dbl_choffrut_twinning` |
| **Word-output length bound (toward word-output pumping):** the δ-level analog of the single-symbol `output_len_le` — with transition outputs `≤ L`, a branch output after reading `w` has length `≤ R + L·|w|` (`≤ L·|w|` for empty-residual starts). The linearly-growing delay bound that twinning later sharpens to a constant; the foundational ingredient a word-output pumping argument needs | `rawSucc_residual_bound`, `rawRun_residual_bound`, `rawRun_output_len_le` |
| **Word-output paths (toward word-output pumping):** `DPathN`, a δ-native path emitting a *word* per step (the analog of `PathN` with no single-symbol restriction), with inversion lemmas and an exact correspondence to the determinizer's branch outputs (`mem_rawRun_iff_dpath`, `mem_rawRun_iff_dpath_start`) — the trajectory structure a word-output pigeonhole/pumping argument runs over | `DPathN`, `dpath_zero_inv`, `dpath_step_inv`, `mem_rawRun_iff_dpath`, `mem_rawRun_iff_dpath_start` |
| **Composability of word-output paths (toward word-output pumping):** `DPathN` runs compose (`DPathN_append`) and decompose at any prefix length (`DPathN_split`); decomposition exposes the state after reading the first `k` letters, the lever a state-pair pigeonhole over `Fin N × Fin N` needs to locate a common loop between two runs on a shared input | `DPathN_append`, `DPathN_split` |
| **Common loop for two word-output runs (toward word-output pumping):** the combinatorial heart, obtained by *reducing* to the single-symbol `two_run_loop` — `δ`'s output-erasure is a real-time single-symbol transducer with identical state behaviour, a `DPathN` run maps to an erasure run and back with recovered outputs, so two runs on a common input longer than `N²` share a nonempty looping infix | `erase`, `erase_realtime`, `erase_of_dpath`, `dpath_of_erase`, `dpath_two_run_loop` |
| **δ-native twinning framework (toward word-output pumping):** `DReaches`/`DLoops`/`DTwinning` restate twinning over `DPathN`, reusing the `delay`/`pdist` word machinery; `dpath_output_len` bounds a run's output by `L·(steps)` and `dpath_pdist_le_steps` gives the `L`-scaled base case `pdist ≤ L·(n₁+n₂)` — the inputs to the eventual constant-bound induction | `dpath_output_len`, `DLoops`, `DReaches`, `DTwinning`, `dpath_pdist_le_steps` |
| **State list + inductive step (toward word-output pumping):** the word-output analog of `PathN.run_list2` — a visited-state list with a splitting property preserving the *actual* output decomposition for any `i ≤ j` cut — plus `dpath_len` (steps = input length) and the loop-removal delay-preservation step from `DTwinning`. All five ingredients of the `~2LN²` induction are now assembled | `dpath_len`, `DPathN.run_list`, `dpath_delay_loop_removal` |
| **The word-output case CLOSED — twinning ⟹ Choffrut, no single-symbol restriction:** the strong common loop (`dpath_two_run_loop_out`, built from `DPathN.run_list` so it preserves the original output decomposition) drives a strong-recursion bound `pdist ≤ 2·L·N²` (`dpath_twinning_pdist_bound_aux`), yielding a constant `dBoundedDelay` from `DTwinning`; fed to `choffrut_subsequential`, a **functional `DTwinning` word-output NFT is realized by a finite subsequential transducer** — the genuinely nondeterministic, multi-letter-output case | `dpath_two_run_loop_out`, `dpath_twinning_pdist_bound_aux`, `dtwinning_bounded_delay`, `dBoundedDelay_of_dtwinning`, `choffrut_subsequential_of_twinning_word` |
| **Determinism subsumed by twinning (word outputs):** a deterministic word-output NFT satisfies `DTwinning` (the analog of `inputDet_twinning`), via run uniqueness — so the twinning route strictly generalizes the deterministic one | `dpath_unique`, `dtwinning_of_deterministic` |
| **Toward word-output necessity (bounded delay ⟹ twinning):** the pumping engine — a `DLoops` loop iterates and a reach-then-loop pumps (`dpath_loops_pow`, `dpath_reaches_loop_pow`), and under `dBoundedDelay` the determinizer caps the prefix-distance of every pumped pair (`dpath_pump_bounded`); the first necessity sub-lemma shows a co-reachable loop emitting different lengths on its two sides forces unbounded delay | `dpath_loops_pow`, `dpath_reaches_loop_pow`, `dpath_pump_bounded`, `dpath_loop_length_mismatch_unbounded` |
| **The full word-output equivalence `DTwinning ⇔ dBoundedDelay`:** the necessity direction mirrors the single-symbol case analysis (divergent / desynchronized / incomparable / non-conjugate loops, the last via the reused Fine–Wilf core `conj_of_synced`), pumping through `dpath_pump_bounded`, assembled in `dpath_bounded_delay_twinning`; with the `2·L·N²` sufficiency this packages as the equivalence — the word-output analog of `twinning_iff_bounded_delay` | `dpath_diverge_loop_unbounded`, `dpath_notsynced_loop_unbounded`, `dpath_noncomparable_nonsilent_unbounded`, `dpath_loop_unbounded`, `dpath_bounded_delay_twinning`, `dtwinning_iff_dBoundedDelay` |
| **Input-ε moves (first step):** relaxing the real-time assumption to steps that read no input letter. Bounded delay forces an ε-input *loop* (a run from a state back to itself on empty input) to be silent — pumping an output-emitting ε-input loop would reach a fixed state on a fixed input with unbounded output, contradicting `HasBoundedDelay` (which does not assume real-time). This is the structural prerequisite for ε-removal; input length is also bounded by step count (the ε-input relaxation of `realtime_len`), and — stronger — bounded delay bounds *every* ε-input run's output by `K`, so each ε-closure output is a word of length `≤ K`: finitely many over a finite alphabet, which is what makes ε-removal terminate | `pathN_eps_loop_pow`, `reaches_eps_loop_pow`, `bounded_delay_eps_loop_silent`, `PathN_input_le_steps`, `bounded_delay_eps_run_output_le` |
| **ε-removal and Choffrut for ε-input transducers** *(fully proved)*: `EpsClosure` defines ε-reachability with accumulated output; `eps_removal` (under natural decidability hypotheses) constructs a compressed word-output real-time transition matching the original relation with bounded delay transferred; `choffrut_eps` derives the **full Choffrut theorem with no real-time restriction** by composing with the proved `choffrut_subsequential`. **0 sorry, 0 Classical.choice** | `EpsClosure`, `eps_removal`, `choffrut_eps` |
| **`EpsBlock` and the single-letter run correspondence** (the building block of the run-factoring): every `PathN` run on a single input letter `[a]` decomposes as `EpsClosure ++ letter-step ++ EpsClosure`, and conversely every such block lifts to a single-letter `PathN` run. With the `EpsClosure ⇄ PathN` bridges, this gives the per-letter ingredient the multi-letter run-factoring (`eps_removal`) would induct over. All four bridge directions proved choice-free | `EpsClosure.toPathN`, `PathN.toEpsClosure`, `EpsClosure.append`, `EpsBlock`, `EpsBlock.inv`, `EpsBlock.toPathN`, `PathN.toEpsBlock` |
| **Per-letter run-factoring** (lifting `EpsBlock` to multi-letter): `PathN.split_letter` decomposes a `PathN` run on `a :: w` into one `EpsBlock` consuming `a` plus a sub-run on `w`; `PathN.join_letter` reassembles them. The empty-input bookends (`PathN.split_empty`, `PathN.join_empty`) go to/from `EpsClosure` directly. Together these are the inductive step the multi-letter factoring in `eps_removal` would assemble | `PathN.split_letter`, `PathN.join_letter`, `PathN.split_empty`, `PathN.join_empty` |
| **Multi-letter run-factoring correspondence `PathN ⇄ EpsFactored`** (the structural core of ε-removal, both directions proved choice-free): `EpsFactored` decomposes a `PathN` run on any input `u` into a leading `EpsClosure` (for `u=[]`) or a chain of `EpsBlock`s, one per consumed letter, and conversely. This is the run-factoring correspondence that `eps_removal` uses; the concrete construction of `δ'`, `φ'`, `P₀'` and the bounded-delay transfer are also proved | `EpsFactored`, `PathN.toEpsFactored`, `EpsFactored.toPathN` |
| **`DPathN ⇄ EpsFactored` bridge** (under δ-matching conditions): `DPathN_toEpsFactored` (δ-soundness → DPathN gives EpsFactored); `EpsFactored_toDPathN` (δ-completeness → EpsFactored decomposes into DPathN + trailing EpsClosure). Connects the determinizer's `rawRun` to the Transducer's `realizes` | `DPathN_toEpsFactored`, `EpsFactored_toDPathN` |
| **Conditional ε-removal: the full correspondence + delay transfer (PROVED)**: under matching conditions on `δ'`/`φ'`/`P₀'` (soundness + completeness of δ-transitions, starts, and final outputs), `nftRel δ' φ' P₀'` equals `realizes T` AND `dBoundedDelay` transfers from `HasBoundedDelay T K`. **ALL the algebraic content of ε-removal is proved**; the construction of matching `δ'`/`φ'`/`P₀'` under decidability is `eps_removal` | `eps_removal_of_match` |
| **Choffrut's theorem for ε-input transducers (conditional, FULLY PROVED)**: given matching `δ'`/`φ'`/`P₀'`, the determinized subsequential transducer `detSubseq δ' φ' P₀'` realizes the same relation as `T` — the full Choffrut closure theorem with **no real-time restriction**, 0 sorry, 0 Classical.choice. Users of concrete transducers supply their matching data directly | `choffrut_eps_of_match` |
| **ε-removal under decidability, sorry-free (`eps_removal`, `choffrut_eps`, FULLY PROVED)**: under natural decidability hypotheses (decidable EpsClosure/EpsBlock/start/accept, global ε-output bound, unique accepting ε-closure output), the compressed `δ'`/`φ'`/`P₀'` are constructed via filtering `pairsLE` and verified against the matching conditions, then `eps_removal_of_match` applies. **0 sorry, 0 Classical.choice** | `eps_removal`, `choffrut_eps` |
| Twinning ⟹ the output delay is invariant under pumping a common loop | `twinning_iterate`, `twinning_delay_indep` |
| The prefix metric on words is a genuine metric; bounded variation defined | `pdist`, `pdist_eq_zero`, `pdist_comm`, `pdist_triangle`, `twinning_pdist_iterate`, `BoundedVariation` |
| Twinning ⟹ a common loop that makes outputs diverge is silent | `lcp_append_of_diverge`, `twinning_diverge_loop` |
| Twinning ⟹ one shared loop never grows the imbalance; run-splitting primitive | `twinning_loop_pdist`, `PathN.split` |
| Pigeonhole principle (counting + witness forms), built from scratch, choice-free | `pigeonhole_nat`, `nodup_length_le_card`, `exists_dup_of_not_nodup`, `pigeonhole` |
| Pumping lemma: a run longer than the state set contains a non-empty loop | `PathN.run_list2`, `PathN.find_loop` |
| Product pigeonhole `Fin N × Fin N`; injection pigeonhole; real-time length | `pigeonhole_prod`, `nodup_length_le_of_inj`, `realtime_len` |
| Two runs on a common input (length > N²) share a loop on a common infix | `two_run_loop` |
| Base case: output length ≤ #steps; `pdist` of two runs ≤ total #steps | `output_len_le`, `input_len_le`, `pdist_le_steps` |
| `delay` is right-congruent; removing a loop preserves the output delay | `delay_congr_right`, `delay_loop_removal` |
| **Twinning ⟹ bounded delay** (`pdist ≤ 2N²`), real-time transducers | `twinning_bounded_delay`, `twinning_hasBoundedDelay` |
| Divergent growth of `pdist`; a divergent non-silent loop ⟹ unbounded delay | `pdist_append_diverge`, `diverge_loop_unbounded` |
| `pdist` dominates length difference; a length-mismatched loop ⟹ unbounded delay | `pdist_ge_length_diff`, `loop_length_mismatch_unbounded` |
| A loop that *eventually* diverges ⟹ unbounded delay | `loop_eventually_diverge_unbounded` |
| Equal-length loops, aligned (zero-lag) distinct ⟹ unbounded delay | `lcp_lt_of_length_eq_of_ne`, `aligned_loop_unbounded` |
| Equal-length loops, conjugate (`β₁·w = w·β₂`) ⟹ constant delay `|w|` (bounded) | `conjugate_overhang_const`, `conjugate_loop_pdist_const` |
| Conjugacy de-powering (Fine–Wilf algebraic core): `β₁ⁿx = xβ₂ⁿ ⟹ β₁x = xβ₂`, equal lengths | `pow_eq_pow_of_length_eq`, `pow_append_swap`, `depower_conjugacy` |
| Commutation theorem (Lyndon–Schützenberger): `uv = vu ⟹ u, v are powers of a common word` | `commute_powers`, `wpow_add` |
| Periodic compatibility `β₁ᴾw = wβ₂ᴾ` (P≥1) ⟹ conjugate ⟹ constant delay `|w|` | `periodic_loop_pdist_const` |
| Short-lag synchrony (`\|w\| ≤ \|β₁\|`) at iterations 1–2 ⟹ conjugate `β₁w = wβ₂` (no pigeonhole) | `conj_of_synced_short` |
| Short-lag equal-length necessity: non-conjugate loop with `\|w\| ≤ \|β₁\|` ⟹ unbounded delay | `notsynced_loop_unbounded`, `shortlag_loop_unbounded` |
| Suffix stabilization (periodicity, one step): `(vᴷ⁺¹).drop((K+1)\|v\|-\|w\|) = (vᴷ).drop(K\|v\|-\|w\|)` | `wpow_drop_one`, `suffix_step` |
| General synchrony ⟹ conjugacy (any lag, no pigeonhole) | `conj_of_synced` |
| **Equal-length necessity, full:** non-conjugate loop ⟹ unbounded delay for *any* lag `w` | `loop_unbounded` |
| Conjugacy preserves the delay around a loop; incomparable bases + non-silent loop ⟹ unbounded | `delay_eq_of_conjugate`, `noncomparable_nonsilent_unbounded` |
| **Necessity: bounded delay ⟹ twinning** (complete case analysis) | `bounded_delay_twinning` |
| **Choffrut delay characterization: twinning ⇔ bounded delay** (real-time, `Fin N`) | `twinning_iff_bounded_delay` |
| A concrete two-state transducer with provably unbounded delay | `Example.badT`, `Example.badT_unbounded` |
| Pumping lemma for rational relations (real-time): the relation pumps along a loop | `pumping_lemma` |
| Pumping down: any accepting run shortens to length ≤ N; non-empty ⟹ short witness | `short_accepting_run`, `realizes_short_witness` |
| Subsequential functions are closed under composition (product machine, both directions) | `Subseq.comp`, `Subseq.comp_realizes`, `Subseq.run_prefix`, `Subseq.run_append` |
| **Trim construction**: every reachable state made co-reachable, preserving the relation | `Trim`, `CoReachable`, `trimT`, `trimT_realizes`, `trimT_isTrim` |
| **Choffrut converse** (subsequential ⟹ twinning): co-reachable loops have equal output length; full conclusion via the bounded-delay bridge | `loop_lengths_of_subseq`, `choffrut_converse`, `Subseq.run_output_bound` |
| Emptiness witnessed by a short run; restriction of a transduction to a regular input domain | `realizes_iff_short`, `restrictDom`, `restrictDom_realizes` |
| **Local characterization of twinning**: the per-loop atom; equal-length necessity | `TwinningLocal`, `twinning_iff_local`, `twinning_loop_eq_length` |
| **Conjugacy necessity**: in the lag regime the loop outputs are conjugate (`β₁·w = w·β₂`); regime trichotomy; full loop structure | `twinning_loop_conjugate`, `delay_nil_left`, `prefix_trichotomy`, `twinning_loop_structure` |
| **Sufficiency**: the local loop structure implies twinning — packaged as the equivalence | `local_structure_twinningLocal`, `twinning_iff_structure` |
| **Conjugacy is a decidable rotation**: `β₁·w = w·β₂` ⟺ `β₂` is the cyclic rotation of `β₁` by `\|w\|` | `conjugate_iff_rotation`, `conjugate_rotation`, `rotation_conjugate` |
| **Boolean reflection** of the structural check; master criterion *twinning ⟺ every loop passes `structOK`* | `structOK`, `structOK_iff`, `twinning_iff_structOK` |
| **Computable run enumeration** for step-function transducers (runs under `#eval`); loop-output detection | `ofStepFn`, `rtRuns`, `mem_rtRuns_iff`, `loopOutputs`, `mem_loopOutputs_iff` |
| **Executable twinning refutation**: one failing loop refutes; the `#eval`-able form over step functions | `refuteTwinning`, `refuteTwinning_ofStepFn` |
| **Finiteness reduction** (the deferred hard direction): loop removal from one loop's structural data; `structOK` everywhere ⟹ bounded delay `2N²` | `delay_loop_removal_struct`, `structOK_pdist_bound`, `structOK_hasBoundedDelay` |
| **The twinning decision criterion** (real-time, `Fin N`): complete two-sided equivalence, both directions finitely grounded; metric = effective | `twinning_decision_criterion`, `structOK_iff_boundedDelay`, `certifyTwinning` |

Both directions of **Kleene's theorem for rational relations** are proved, and the
capstone `kleene` states them together at the structural level: a word relation is
denotable by a rational expression **if and only if** it is realized by some
concrete `FinTransducer` over `Fin n`.

## The model

* **Letter-labeled transitions.** Each transition reads an *optional* input letter
  and writes an *optional* output letter (`Option`); `none` on either tape gives
  ε-moves. This model captures exactly the rational relations.
* **Step-indexed paths.** Runs carry an explicit step count (`PathN`), so every
  induction is a robust induction on `Nat` that survives ε:ε ("silent") moves.
* **States need not be finite** for the closure theorems; finiteness matters only
  for decidability and for the converse of Kleene's theorem, where it is handled
  explicitly via `FinEnc` (a bijection of a state type to `Fin n`) and `FinPres`
  (a finite presentation: decidable start/accept predicates plus finite label
  lists per state pair).

The source is thoroughly commented: every section carries a `/-! ## … -/` doc
comment that states the textbook content in prose and explains how the Lean
definitions and theorem names realize it, so a reader who knows the theory but
not Lean can follow the correspondence.

## The twinning decision procedure

The library proves the **Choffrut delay characterization** (*twinning ⇔ bounded
delay*) and **determinization** (*bounded delay ⇒ subsequential*) in both
directions. On top of that it builds an **effective** form: a machine-checkable —
and partly *executable* — decision criterion for the twinning property, following
the Béal–Carton–Prieur–Sakarovitch analysis.

The chain from the abstract property to running code:

| Layer | Statement | Lean |
| --- | --- | --- |
| Algebraic | the twinning property (global, over all co-reachable loops) | `Twinning` |
| Local | twinning ⟺ every co-reachable loop is lag/reverse-lag **conjugate** or **silent** | `twinning_iff_structure` |
| Conjugacy | each conjugacy check ⟺ a decidable **rotation** test | `conjugate_iff_rotation` |
| Boolean | twinning ⟺ every co-reachable loop passes the boolean `structOK` | `twinning_iff_structOK` |
| Metric | `structOK` everywhere ⟺ bounded delay `2N²` | `structOK_iff_boundedDelay` |
| **Capstone** | the complete two-sided criterion, both directions finitely grounded | `twinning_decision_criterion` |

Two ingredients make this genuinely effective rather than merely classical:

* **Executable enumeration.** A real-time transducer presented by a step
  *function* (`ofStepFn`) gets a computable run enumerator `rtRuns` — proved to
  capture exactly the relational runs (`mem_rtRuns_iff`) — and a loop-output
  detector `loopOutputs`. Both **run under `#eval`**. The demo `demoBadδ` is a
  concrete non-twinning machine whose violation `structOK` detects by
  computation (`#eval … = false`), turned into a proof of `¬ Twinning` by
  `refuteTwinning_ofStepFn`.

* **The finiteness reduction.** The naïve "only check short witnesses" shortcut is
  *false*: the structural condition mentions the (arbitrarily long) reaching
  outputs. The resolution is that the delay-bounding recursion never needs a
  long-reach loop — `two_run_loop` always extracts a *short* synchronized loop
  (length ≤ N²), and `delay_loop_removal_struct` removes it from that single
  loop's structural data alone. `structOK_pdist_bound` runs this recursion using
  the boolean check only on the short loops it extracts, yielding the bound
  `pdist ≤ 2N²` and hence twinning (`structOK_hasBoundedDelay`).

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager). The toolchain is pinned in `lean-toolchain` to `leanprover/lean4:v4.30.0`
and will be fetched automatically. There are **no other dependencies**.

```sh
lake build
```

A successful build type-checks the whole library and prints the axiom audit. To
type-check the single file directly without Lake:

```sh
lean FST.lean
```

## Trust basis

This is a verification artifact, so its trust basis is stated explicitly:

* No `sorry`, no `admit`, and no result depends on `sorryAx` (verified across all
  ~520 declarations, ~9,600 lines).
* The only axioms used are `propext` (propositional extensionality) and
  `Quot.sound` (soundness of quotients) — both standard and part of Lean's core
  logic. `Classical.choice` is **not** used anywhere. Keeping this property was a
  deliberate constraint: the pigeonhole principle, for instance, is built from
  scratch via `filter` because the usual `List.erase` / `List.nodup_range` route has
  core proofs that depend on `Classical.choice`.
* The audit is not a side document: the `#print axioms` block at the bottom of
  `FST.lean` runs on every build, so the claims above are re-checked continuously.

## Scope and what is *not* formalized

The **Choffrut delay characterization** is proved in its metric core, both directions and both
output models, choice-free:

* single-symbol: `twinning_iff_bounded_delay` (twinning ⇔ bounded delay, explicit bound `2N²`),
  assembled from the product pigeonhole `two_run_loop`, loop-removal `delay_loop_removal`, and the
  base case `pdist_le_steps` by strong induction (`twinning_bounded_delay`); the necessity facts
  `loop_length_mismatch_unbounded`, `diverge_loop_unbounded`, and the Fine–Wilf/conjugacy criterion
  `conj_of_synced` for equal-length loops;
* word-output: `dtwinning_iff_dBoundedDelay` (bound `2·L·N²`), the determinizer analog;
* the determinization itself: `choffrut_subsequential` and its twinning/deterministic specializations
  build the subsequential transducer realizing the same relation.

What was **previously out of scope is now formalized**: the converse direction
(*subsequential ⟹ twinning*) is proved as `choffrut_converse`, resting on the
explicit trimming construction (`trimT`, `trimT_realizes`, `trimT_isTrim`) and the
equal-length loop lemma `loop_lengths_of_subseq`. Together with the determinization
direction this closes the Choffrut characterization for trim functional real-time
finite-state transducers: *subsequential ⟺ twinning ⟺ bounded delay*, all three
also shown equivalent to the **effective** boolean criterion (see "The twinning
decision procedure" above).

Still genuinely **not** in scope: decidability of *equivalence* of two
subsequential transducers, *minimization* (a canonical minimal subsequential
form), and the more general two-way / streaming / weighted transducer models. The
*positive* twinning decision is reduced to finitely checkable data
(`twinning_decision_criterion`) but is not packaged as a single executable
`Decidable Twinning` instance — that wiring (enumerating reachable state pairs and
their primitive loops, then folding `structOK` over them) is a well-scoped
remaining step, distinct from the mathematics, which is complete.

### Choffrut for input-ε transducers

Choffrut is lifted from real-time to arbitrary input-ε moves, **fully proved**.  `EpsClosure` defines
ε-reachability with accumulated output.  The run-factoring correspondence (`PathN ⇄ EpsFactored`) is proved
via `EpsFactored`, `PathN.toEpsFactored`, and `EpsFactored.toPathN`: every ε-input `PathN` decomposes into a
leading `EpsClosure` segment plus one `EpsBlock` per consumed letter, and conversely.

`eps_removal_of_match` proves the **full algebraic content** of ε-removal: under matching conditions on
`δ'`/`φ'`/`P₀'` (soundness + completeness of transitions, starts, and final outputs),
`nftRel δ' φ' P₀' x y ↔ realizes T x y` AND `dBoundedDelay δ' P₀' K` from `HasBoundedDelay T K`.  This
assembles the entire correspondence chain `rawRun ↔ DPathN ↔ EpsFactored ↔ PathN`, with the initial
ε-closure handled by `P₀'`, the per-letter blocks by `δ'`, the trailing ε-closure by `φ'`, and the delay
transfer via `Reaches ↔ rawRun`.

`eps_removal` then **constructs** concrete `δ'`, `φ'`, `P₀'` satisfying those matching conditions, under
natural decidability hypotheses (decidable `EpsClosure`/`EpsBlock`/`start`/`accept`, a global ε-closure
output bound, and uniqueness of accepting ε-closure outputs).  The construction filters `pairsLE` — the
finitely many `EpsBlock`/`EpsClosure` outputs over `Fin N` states and `Fin M` outputs, all bounded by `K`
via `bounded_delay_eps_run_output_le`.  `choffrut_eps` chains `eps_removal` with the proved
`choffrut_subsequential` to give the full Choffrut closure with no real-time restriction.

**Bottom line:** The library provides multiple complete paths to Choffrut for ε-input transducers, ALL fully
proved (0 sorry, 0 Classical.choice): `choffrut_eps_of_match` (takes matching data as input),
`choffrut_eps` (constructs the data under decidability), and the real-time word-output versions
(`choffrut_subsequential_of_twinning_word`, etc.) that ε-removal feeds into.

## Repository layout

```
FST.lean                      the library (single self-contained module)
lakefile.toml                 Lake package manifest (library target `FST`)
lean-toolchain                pinned Lean/Lake version
check.sh                      convenience build-and-report script
README.md                     this file
CONTRIBUTING.md               project invariants and how to verify a change
CITATION.cff                  citation metadata
LICENSE                       Apache License 2.0
.github/workflows/ci.yml      build, type-check, and axiom-hygiene audit
.github/workflows/hygiene.yml fast source/repo hygiene checks
.github/dependabot.yml        keeps the GitHub Actions versions current
```

## Citing this work

If you use this formalization or build on its proofs, a citation is appreciated.
GitHub renders the `CITATION.cff` metadata directly ("Cite this repository" in the
sidebar). A BibTeX entry:

```bibtex
@software{lean_fst,
  title        = {Finite-State Transducers in {Lean}~4},
  author       = {Claude, Opus Models Family and Alekseev, Anton},
  year         = {2026},
  version      = {1.0.0},
  license      = {MIT},
  url          = {https://github.com/alexeyev/finite-state-transducers-lean}
}
```

The underlying mathematics is classical; the standard references are Sakarovitch,
*Elements of Automata Theory* (transducers and rational relations), Choffrut's
characterization of subsequential functions, and the Béal–Carton–Prieur–Sakarovitch
analysis of the twinning property (the structure followed by the decision-procedure
section).

## A note on how this was prepared

This development was produced with Anthropic's Claude (Opus models family). The
mathematics is classical, but the formalization — every definition, proof, and the
workarounds for the absence of Mathlib — was written and checked iteratively
against the Lean kernel. The kernel, not the model, is the final arbiter of
correctness: every result type-checks, no proof uses `sorry`, and the axiom audit
that runs on each build confirms the dependency closure stays within `propext` and
`Quot.sound`.

## License

Released under the Beerware License (Revision 42). See [`LICENSE`](LICENSE).
