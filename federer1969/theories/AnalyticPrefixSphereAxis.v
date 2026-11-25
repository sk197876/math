(** Federer (1969), 3.4.8(6), pp. 328–329:
    the original e_j lies on the prefix unit
    sphere and supplies the actual Haar orbit basepoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom InnerProductUP InnerNorm InnerMetric OrthonormalFamilies
  InnerNormalization AnalyticPrefixSphereAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_sphere_axis_member]: the
    original e_j is a unit vector perpendicular
    to every later basis vector, as required
    by V(h)=h(e_j), 3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_axis_member (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X):
  orthonormal_family B e ->forall j:'I_n,
    @analytic_prefix_unit_sphere R X B hB n e (j:nat).+1 (e j).
Proof.
move=>hON j;split.
- exact:(@orthonormal_norm1 R X B hB (Finite.clone 'I_n _) e hON j).
- move=>i hi;have hDiff:j!=i.
    apply/eqP=>hEqual;move:hi;by rewrite -hEqual ltnn.
  by rewrite hON (negbTE hDiff).
Qed.
