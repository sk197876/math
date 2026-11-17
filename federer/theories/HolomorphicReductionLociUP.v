(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    the original reduction sets A_j, B_j, C_m and E_m
    are specified by their exact membership equations.
    The specifications assume no Borel, measure, depth,
    or stratification conclusion. Array index j denotes
    the printed B_(j+1); all other indices are literal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP SymmetricForms HolomorphicGermFormsSealed Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_nonzero_holomorphic_directional_jet]: the
    original positive-order directional test in B_j,
    3.4.8(2), p. 326. Lower derivatives need not
    vanish, and the direction need not have unit norm. *)
Definition has_nonzero_holomorphic_directional_jet (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X)) (v:X):Prop:=
  exists k,(0<k)%N /\
    @HolomorphicGermForms.value R X NX hNX 0 k alpha [tuple v|_<k]<>0.
Arguments has_nonzero_holomorphic_directional_jet {R X NX} hNX alpha v.

(** Source for [is_holomorphic_reduction_loci]: the original
    membership laws for A_j, B_j, C_m and E_m,
    3.4.8(2), p. 326. Coordinate subrings, rotated
    ideals, basis vectors and actual coordinate germs
    are the original inputs. Empty and full prefixes remain. *)
Record is_holomorphic_reduction_loci (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) n (O:Type)
    (e:'I_n->X) (gamma:'I_n->@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)
    (Q:nat->set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0))
    (rotated:O->set (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0))
    (A:'I_n.+1->set O) (B C:'I_n->set O) (E:'I_n.+1->set O):Prop:={
  (** Source for [holomorphic_reduction_A_membership]: a nonzero
      original rotated germ belongs to Q_j; A_0 is
      empty, 3.4.8(2), p. 326. *)
  holomorphic_reduction_A_membership:forall j g,A j g <->
    (0<j)%N /\exists alpha,rotated g alpha /\Q j alpha /\alpha<>0;
  (** Source for [holomorphic_reduction_B_membership]: the actual
      positive directional derivative test for some original
      rotated coordinate germ, 3.4.8(2), p. 326. *)
  holomorphic_reduction_B_membership:forall j g,B j g <->
    exists alpha,rotated g alpha /\Q (j:nat).+1 alpha /\
      has_nonzero_holomorphic_directional_jet hNX alpha (e j);
  (** Source for [holomorphic_reduction_C_membership]: the original
      denominators and relations delta_j gamma_j minus L_j
      lie in the rotated ideal, 3.4.8(2), p. 326.
      Each denominator belongs to Q_m outside that ideal. *)
  holomorphic_reduction_C_membership:forall m g,C m g <->
    forall j:'I_n,(m<=j)%N ->exists delta L,
      Q m delta /\~rotated g delta /\Q (m:nat).+1 L /\
      rotated g (delta*gamma j-L);
  (** Source for [holomorphic_reduction_E_membership]: the original
      C_m intersection of all B_j for j>m, minus A_m,
      3.4.8(2), p. 326. *)
  holomorphic_reduction_E_membership:forall m g,E (widen_ord (leqnSn n) m) g <->
    C m g /\(forall j:'I_n,(m<=j)%N ->B j g) /\
      ~A (widen_ord (leqnSn n) m) g;
  (** Source for [holomorphic_reduction_E_last_membership]: the
      original E_n=O(n) minus A_n endpoint,
      3.4.8(2), p. 326. *)
  holomorphic_reduction_E_last_membership:forall g,E ord_max g <->~A ord_max g
}.
