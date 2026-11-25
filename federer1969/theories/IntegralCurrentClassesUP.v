(** Federer (1969), 4.1.24, p. 381: the original
    integral currents, integral flat chains, compact unions,
    and local germ classes. These are independent literal
    membership predicates on the actual current spaces.
    Group structure, inclusion, metric and completeness laws
    remain separate proof obligations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralCurrentClassesUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(fun m=>@current_space R h2 n U hU m).
Local Notation Index:=(smooth_compact_set hNX U).
Local Notation Rect:=(fun m K=>@is_rectifiable_current_supported_in R h2 n m U hU K).

(** Source for [is_rectifiable_current]: R_m(U) is the
    literal union over all compact K of R_(m,K)(U),
    Federer 4.1.24, pp. 380–381. *)
Definition is_rectifiable_current m (T:C m):Prop:=exists K:Index,Rect m K T.

(** Source for [is_integral_current_supported_in]: the positive
    degree condition T and boundary T rectifiable with
    the same K, and the separate I_(0,K)=R_(0,K),
    Federer 4.1.24, p. 381. No negative-degree current
    space or boundary is introduced. *)
Definition is_integral_current_supported_in m (K:Index):C m->Prop:=
  match m as d return C d->Prop with
  |0%N=>Rect 0%N K
  |j.+1=>fun T=>Rect j.+1 K T /\
    Rect j K (@current_boundary R h2 n j U hU T)
  end.

(** Source for [is_integral_current]: the abelian group
    I_m(U) is the original union over all compact
    K of I_(m,K)(U), Federer 4.1.24, p. 381. *)
Definition is_integral_current m (T:C m):Prop:=
  exists K:Index,is_integral_current_supported_in K T.

(** Source for [is_integral_flat_current_supported_in]: script-F_(m,K)
    consists exactly of the actual currents R+boundary S,
    with both rectifiable terms in the same K,
    Federer 4.1.24, p. 381. *)
Definition is_integral_flat_current_supported_in m (K:Index) (T:C m):Prop:=
  exists A:C m,exists S:C m.+1,
    Rect m K A /\Rect m.+1 K S /\
    T=A+@current_boundary R h2 n m U hU S.

(** Source for [is_integral_flat_current]: the original
    script-F_m(U) is the union over every compact
    K of script-F_(m,K)(U), Federer 4.1.24, p. 381. *)
Definition is_integral_flat_current m (T:C m):Prop:=
  exists K:Index,is_integral_flat_current_supported_in K T.

(** Source for [is_locally_rectifiable_current]: the literal
    pointwise germ definition on p. 381 of 4.1.24.
    Each x in U has an original compactly supported
    rectifiable representative S with x outside spt(T-S).
    No global finite mass or common compact is imposed. *)
Definition is_locally_rectifiable_current m (T:C m):Prop:=
  forall x,U x->exists S:C m,is_rectifiable_current S /\
    ~@current_support R h2 n U hU m (T-S) x.

(** Source for [is_locally_integral_current]: the same
    original germ condition for I_m, Federer 4.1.24,
    p. 381, retaining the freedom to choose a different
    global integral representative at every point. *)
Definition is_locally_integral_current m (T:C m):Prop:=
  forall x,U x->exists S:C m,is_integral_current S /\
    ~@current_support R h2 n U hU m (T-S) x.

(** Source for [is_locally_integral_flat_current]: the original
    local integral-flat class, Federer 4.1.24, p. 381.
    Membership uses the actual difference support and the
    original global compact union, without a global mass bound. *)
Definition is_locally_integral_flat_current m (T:C m):Prop:=
  forall x,U x->exists S:C m,is_integral_flat_current S /\
    ~@current_support R h2 n U hU m (T-S) x.
End IntegralCurrentClassesUP.
