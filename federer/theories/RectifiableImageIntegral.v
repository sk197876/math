(** Federer (1969), 4.1.24, pp. 380–382: each
    original image approximant is an integral current.
    The source polyhedral boundary has the same compact
    index, and the existing actual Lipschitz pushforward
    commutes with boundary. This proves the subsidiary
    mass-density assertion without assuming a stronger
    rectifiable structure theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic SmoothCompactSet CurrentSpaces CurrentBoundary
  CurrentMassSealed PolyhedralCurrentBoundary PolyhedralCurrentFlat
  CurrentFlatLipschitzPushforwardBoundary RectifiableCurrentApproximationUP
  RectifiableCurrentWitnesses IntegralCurrentClassesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableImageIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set hNX U.
Local Notation C:=(fun d=>@current_space R h2 n U hU d).
Local Notation Approx:=(fun d=>@is_rectifiable_image_approximant R h2 n d U hU K).

(** Source for [rectifiable_image_approximant_boundary]: the
    actual boundary of an image witness is another
    original image witness, with the same source compact
    and target K. This is the boundary argument
    behind integral mass density in 4.1.24, p. 382. *)
Theorem rectifiable_image_approximant_boundary m (Q:C m.+1):
  Approx m.+1 Q->Approx m (@current_boundary R h2 n m U hU Q).
Proof.
move=>[d [Z [hZ [A [f [hImage [hLip [P [hP [hAK <-]]]]]]]]]].
pose B:=@current_boundary R h2 d m Z hZ P.
pose hB:=@integral_polyhedral_current_boundary_supported R h2 d m Z hZ A P hP.
exists d,Z,hZ,A,f,hImage,hLip,B,hB;split;first exact:hAK.
unfold polyhedral_lipschitz_image;apply:esym.
exact:current_flat_lipschitz_pushforward_boundary.
Qed.

(** Source for [rectifiable_image_approximant_integral]: each
    original image witness is in I_(m,K), using the
    separate degree-zero clause and actual positive boundary,
    as required for mass density in 4.1.24, p. 382. *)
Theorem rectifiable_image_approximant_integral m (Q:C m):
  Approx m Q->@is_integral_current_supported_in R h2 n U hU m K Q.
Proof.
case:m Q=>[|j] Q hQ.
- exact:rectifiable_image_approximant_is_rectifiable hQ.
- split;first exact:rectifiable_image_approximant_is_rectifiable hQ.
  apply:rectifiable_image_approximant_is_rectifiable.
  exact:rectifiable_image_approximant_boundary hQ.
Qed.

(** Source for [integral_current_mass_dense_in_rectifiable]:
    the printed subsidiary assertion that I_(m,K) is
    M dense in R_(m,K), Federer 4.1.24, p. 382.
    The arbitrary degree also supplies the stated next
    degree assertion. Both keep exactly the original K. *)
Theorem integral_current_mass_dense_in_rectifiable m (T:C m):
  @is_rectifiable_current_supported_in R h2 n m U hU K T->
  forall epsilon:R,0<epsilon->exists Q:C m,
    @is_integral_current_supported_in R h2 n U hU m K Q /\
    (@CurrentMass.value R h2 n m U hU (T-Q)<epsilon%:E)%E.
Proof.
move=>hT epsilon hEpsilon.
have[Q [hQ hError]]:=hT epsilon hEpsilon.
exists Q;split;last exact:hError.
exact:rectifiable_image_approximant_integral hQ.
Qed.
End RectifiableImageIntegral.
