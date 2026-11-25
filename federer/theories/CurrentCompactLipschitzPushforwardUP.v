(** Federer (1969), 4.1.14, pp. 370–371: independently specify
    the original compact Lipschitz image by its exact flat target
    and every printed smooth-approximation condition. Existence,
    uniqueness, linearity and sharp bounds are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP SmoothCompactSet CurrentSpaces
  FlatCurrentsUP FlatCurrentSpaces CurrentLipschitzCompactImage
  CurrentOpenIdentitySmooth CurrentCompactPushforwardAlgebra
  CurrentSmoothApproximationUP CurrentFlatSequenceLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzPushforwardUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V
  hU f hImage hLocal K).
Local Notation CU:=(@current_space R h2 n U hU m).
Local Notation CV:=(@current_space R h2 nu V hV m).

(** Source for [is_current_compact_lipschitz_image]: the actual
    f#T belongs to F_(m,f(K))(V) and satisfies every displayed
    convergence condition in Federer 4.1.14, p. 370. S is any
    original flat representative under inclusion from any open
    neighbourhood Z of K. E is any compact target neighbourhood
    of f(K), and the derivative cap remains restricted to K. *)
Definition is_current_compact_lipschitz_image (T:CU) (Q:CV):Prop:=
  @is_flat_current_supported_in R h2 nu m V hV fK Q /\
  forall (E:smooth_compact_set hNY V),
    (forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x))->
    forall (Z:set X)
      (hZ:forall x,Z x->norm_domain_interior NX Z x)
      (hZU:forall x,Z x->U x)
      (hKZ:smooth_compact_carrier K `<=` Z)
      (S:@current_space R h2 n Z hZ m)
      (hS:@is_flat_current_supported_in R h2 n m Z hZ
        (@current_compact_index_in_open R n U Z K hKZ) S),
    @current_compact_map_pushforward R h2 n n Z U hZ hU
      (fun x:X=>x) hZU (@current_open_identity_smooth R n Z hZ)
      m S (@flat_supported_current_compact R h2 n m Z hZ
        (@current_compact_index_in_open R n U Z K hKZ) S hS)=T->
    forall (g:nat->X->Y)
      (hG:@is_current_smooth_approximation R n nu Z V
        (@current_compact_index_in_open R n U Z K hKZ) f g),
    @is_current_flat_sequence_limit R h2 nu m V hV E
      (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
        (g i) (current_smooth_approximation_image hG i)
        (current_smooth_approximation_class hG i) m S
        (@flat_supported_current_compact R h2 n m Z hZ
          (@current_compact_index_in_open R n U Z K hKZ) S hS)) Q.

(** Source for [is_current_compact_lipschitz_pushforward]: the
    actual linear map F_(m,K)(U)->F_(m,f(K))(V) with the original
    defining approximation law, Federer 4.1.14, pp. 370–371.
    The independent specification assumes no selected limit,
    integrability, normality or bound of a candidate map. *)
Definition is_current_compact_lipschitz_pushforward
    (P:Hom (@flat_current_space R h2 n m U hU K)
      (@flat_current_space R h2 nu m V hV fK)):Prop:=
  forall z,is_current_compact_lipschitz_image
    (@flat_current_inclusion R h2 n m U hU K z)
    (@flat_current_inclusion R h2 nu m V hV fK (P z)).
End CurrentCompactLipschitzPushforwardUP.
