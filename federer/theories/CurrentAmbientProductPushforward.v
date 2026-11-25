(** Federer (1969), 4.1.11, p. 366: the
    original Cartesian product commutes with compact
    smooth images on the whole Euclidean spaces.
    Reuse the proved arbitrary-domain product theorem;
    identify only its equal full-domain presentations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianCompactCurrents
  CurrentCartesianMapClass CurrentCartesianMapPullback CurrentCartesianProductPushforward
  CurrentCompactPushforwardAlgebra CurrentCompactMapDomainTransport CurrentAmbientCartesianProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientProductPushforward.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m mu n nu:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation Source := (@euclidean_cartesian_set R m mu (Full m) (Full mu)).
Local Notation Target := (@euclidean_cartesian_set R n nu (Full n) (Full nu)).
Local Notation hSource := (@current_cartesian_domain_open R m mu
  (Full m) (Full mu) (hFull m) (hFull mu)).
Local Notation hTarget := (@current_cartesian_domain_open R n nu
  (Full n) (Full nu) (hFull n) (hFull nu)).
Variables (f:R_n R m->R_n R n) (g:R_n R mu->R_n R nu).
Hypothesis hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (Full m) f.
Hypothesis hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R mu))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) (Full mu) g.
Local Notation FImage := (fun (x:R_n R m) (_:True)=>Logic.I).
Local Notation GImage := (fun (y:R_n R mu) (_:True)=>Logic.I).
Local Notation FClass := (@current_cartesian_factor_open_class R m n (Full m) (hFull m) f hf).
Local Notation GClass := (@current_cartesian_factor_open_class R mu nu (Full mu) (hFull mu) g hg).
Local Notation Map := (@euclidean_cartesian_map R m mu n nu f g).
Local Notation Image := (fun z hz=>@current_cartesian_map_domain_image R m mu n nu
  (Full m) (Full mu) (Full n) (Full nu) f g FImage GImage z hz).
Local Notation FullImage := (fun (z:R_n R (m+mu)%N) (_:True)=>Logic.I).
Local Notation MapClass := (@current_cartesian_map_on_open_product_smooth R m mu n nu f g hf hg
  (Full m) (Full mu) (hFull m) (hFull mu)).
Local Notation MapGlobal := (@current_cartesian_map_smooth R m mu n nu f g hf hg).
Variables i j:nat.
Variable S:@current_space R h2 m (Full m) (hFull m) i.
Variable T:@current_space R h2 mu (Full mu) (hFull mu) j.
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m (Full m) (hFull m) i S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R mu)))
  (@current_support R h2 mu (Full mu) (hFull mu) j T).
Local Notation Raw := (@CartesianCurrentProduct.value R h2 m mu i j
  (Full m) (Full mu) (hFull m) (hFull mu) S T).
Local Notation hRaw := (@current_cartesian_compact_currents R h2 m mu i j
  (Full m) (Full mu) (hFull m) (hFull mu) S T hS hT).
Local Notation Product := (@current_ambient_cartesian_product R h2 m mu i j S T).
Local Notation hProduct := (@current_ambient_cartesian_product_compact R h2 m mu i j S T hS hT).
Local Notation FS := (@current_compact_map_pushforward R h2 m n (Full m) (Full n)
  (hFull m) (hFull n) f FImage FClass i S hS).
Local Notation GT := (@current_compact_map_pushforward R h2 mu nu (Full mu) (Full nu)
  (hFull mu) (hFull nu) g GImage GClass j T hT).

(** Source for [current_ambient_product_pushforward]:
    (f times g)#(S times T)=f#S times g#T on the
    original whole spaces, supporting the affine prism
    transfer and triangle associativity proof in Federer
    4.1.11, p. 366. Arbitrary compact currents and
    all degrees remain allowed. The map hypotheses are
    satisfied by the original affine and polynomial maps. *)
Theorem current_ambient_product_pushforward:
  @current_compact_map_pushforward R h2 (m+mu)%N (n+nu)%N
    (Full (m+mu)%N) (Full (n+nu)%N) (hFull (m+mu)%N) (hFull (n+nu)%N)
    Map FullImage MapGlobal (i+j)%N Product hProduct=
  @current_ambient_cartesian_product R h2 n nu i j FS GT.
Proof.
have hDomain:=@current_compact_map_domain_transport R h2 (m+mu)%N (n+nu)%N
  Source (Full (m+mu)%N) Target (Full (n+nu)%N) hSource (hFull (m+mu)%N)
  hTarget (hFull (n+nu)%N) (@current_cartesian_full_domain R m mu)
  (@current_cartesian_full_domain R n nu) Map Image FullImage MapClass MapGlobal
  (i+j)%N Raw hRaw hProduct.
have hNatural:=@current_cartesian_product_pushforward R h2 m mu n nu
  (Full m) (Full mu) (Full n) (Full nu) (hFull m) (hFull mu) (hFull n) (hFull nu)
  f g hf hg FImage GImage i j S T hS hT.
rewrite /current_compact_map_pushforward in hDomain.
rewrite hNatural in hDomain.
exact:hDomain.
Qed.
End CurrentAmbientProductPushforward.
