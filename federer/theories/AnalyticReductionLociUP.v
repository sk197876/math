(** Federer (1969), 3.4.8(2), p. 326:
    the original reduction sets A_j, B_j, C_m and E_m
    are specified by their exact membership equations.
    The specifications assume no Borel, measure, depth,
    or stratification conclusion. Array index j denotes
    the printed B_(j+1); all other indices are literal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermUP AnalyticGermJetsSealed AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_nonzero_analytic_directional_jet]: the
    original positive-order directional test in B_j,
    3.4.8(2), p. 326. Lower derivatives need not
    vanish, and the direction need not have unit norm. *)
Definition has_nonzero_analytic_directional_jet (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (alpha:analytic_germ_space hNX (0:X)) (v:X):Prop:=
  exists k,(0<k)%N /\
    @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|) hNX
      (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
      (@AnalyticGermJets.value R X NX hNX 0 k alpha)<>0.

(** Source for [is_analytic_reduction_loci]: the original
    membership laws for A_j, B_j, C_m and E_m,
    3.4.8(2), p. 326. Coordinate subrings, rotated
    ideals, basis vectors and actual coordinate germs
    are the original inputs. Empty and full prefixes remain. *)
Record is_analytic_reduction_loci (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (O:Type)
    (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
    (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
    (rotated:O->set (@analytic_germ_ring R X NX hNX 0))
    (A:'I_n.+1->set O) (B C:'I_n->set O) (E:'I_n.+1->set O):Prop:={
  (** Source for [analytic_reduction_A_membership]: a nonzero
      original rotated germ belongs to Q_j; A_0 is
      empty, 3.4.8(2), p. 326. *)
  analytic_reduction_A_membership:forall j g,A j g <->
    (0<j)%N /\exists alpha,rotated g alpha /\Q j alpha /\alpha<>0;
  (** Source for [analytic_reduction_B_membership]: the actual
      positive directional derivative test for some original
      rotated coordinate germ, 3.4.8(2), p. 326. *)
  analytic_reduction_B_membership:forall j g,B j g <->
    exists alpha,rotated g alpha /\Q (j:nat).+1 alpha /\
      has_nonzero_analytic_directional_jet alpha (e j);
  (** Source for [analytic_reduction_C_membership]: the original
      denominators and relations delta_j gamma_j minus L_j
      lie in the rotated ideal, 3.4.8(2), p. 326.
      Each denominator belongs to Q_m outside that ideal. *)
  analytic_reduction_C_membership:forall m g,C m g <->
    forall j:'I_n,(m<=j)%N ->exists delta L,
      Q m delta /\~rotated g delta /\Q (m:nat).+1 L /\
      rotated g (delta*gamma j-L);
  (** Source for [analytic_reduction_E_membership]: the original
      C_m intersection of all B_j for j>m, minus A_m,
      3.4.8(2), p. 326. *)
  analytic_reduction_E_membership:forall m g,E (widen_ord (leqnSn n) m) g <->
    C m g /\(forall j:'I_n,(m<=j)%N ->B j g) /\
      ~A (widen_ord (leqnSn n) m) g;
  (** Source for [analytic_reduction_E_last_membership]: the
      original E_n=O(n) minus A_n endpoint,
      3.4.8(2), p. 326. *)
  analytic_reduction_E_last_membership:forall g,E ord_max g <->~A ord_max g
}.
