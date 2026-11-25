(** Federer (1969), 3.2.23, p. 260: the characteristic
    cutoffs of the two parameter sets multiply to the cutoff of
    their Cartesian product. This supports the separated integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap TotalScalarCutoff
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_cartesian_scalar_cutoff_product]: supporting
    exact subset-integrand equality in Federer 3.2.23, p. 260,
    by the zero-extension convention of 2.4.10, p. 85.
    No measurability assumption is needed for this pointwise law. *)
Lemma euclidean_cartesian_scalar_cutoff_product (R:realType) m mu
    (A:set (R_n R m)) (B:set (R_n R mu)) (J:R_n R m->R) (K:R_n R mu->R):
  total_scalar_cutoff (euclidean_cartesian_set A B)
    (fun p=>J (euclidean_block_split p).1*K (euclidean_block_split p).2)=
  (fun p=>total_scalar_cutoff A J (euclidean_block_split p).1*
    total_scalar_cutoff B K (euclidean_block_split p).2).
Proof.
apply:funext=>p.
have [hA|hA]:=pselect (A (euclidean_block_split p).1).
- have [hB|hB]:=pselect (B (euclidean_block_split p).2).
  + have hInside:euclidean_cartesian_set A B p:=conj hA hB.
    by rewrite (total_scalar_cutoff_on _ hInside) (total_scalar_cutoff_on J hA) (total_scalar_cutoff_on K hB).
  + have hNot:~euclidean_cartesian_set A B p.
      move=>[_ hBx]; exact:hB hBx.
    by rewrite (total_scalar_cutoff_off _ hNot) (total_scalar_cutoff_off K hB) mulr0.
- have hNot:~euclidean_cartesian_set A B p.
    move=>[hAx _]; exact:hA hAx.
  by rewrite (total_scalar_cutoff_off _ hNot) (total_scalar_cutoff_off J hA) mul0r.
Qed.

(** Source for [total_embedded_scalar_cutoff_graph]: supporting
    exact extended integrand in the product area calculation of
    Federer 3.2.23, p. 260, by the zero-extension law of
    2.4.10, p. 85. The total extended embedding and the
    partial real-function embedding have equal graphs after cutoff. *)
Lemma total_embedded_scalar_cutoff_graph (R:realType) (X:Type)
    (A:set X) (J:X->R) x (z:extended_real_line R):
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (partial_function_total (fun x=>((J x)%:E:extended_real_line R)))) x z <->
  partial_function_graph (real_total_integrand (total_scalar_cutoff A J)) x z.
Proof.
rewrite real_total_integrand_graph.
have [hx|hx]:=pselect (A x).
- rewrite (@partial_function_zero_extension_on X (extended_real_line R) 0 A _ x z hx)
    (total_scalar_cutoff_on J hx).
  by [].
- rewrite (@partial_function_zero_extension_off X (extended_real_line R) 0 A _ x z hx)
    (total_scalar_cutoff_off J hx).
  split=>h; exact:esym h.
Qed.
