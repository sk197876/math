(** Federer (1969), 4.1.18, p. 374: the
    original homotopy formula for each fixed-z
    translation, before averaging. Reuse 4.1.9
    for arbitrary currents and identify equal-domain
    presentations internally.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentDomainTransport CurrentTranslationChain
  CurrentTranslationHomotopy CurrentTranslationEndpointImages CurrentTranslations
  EuclideanAdditiveGroup CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyGeometry CurrentHomotopySliceClass CurrentHomotopyEndpointProper
  CurrentHomotopyBoundaryCylinder CurrentHomotopyPositiveFormula CurrentHomotopyZeroFormula
  CurrentDeformationChainSealed CurrentDeformationChainCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTranslationChainHomotopy.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable z:X.
Local Notation tau:=(@euclidean_translation R n z).
Local Notation H:=(@current_translation_homotopy R n z).
Local Notation hH:=(@current_translation_homotopy_laws R n z).
Local Notation hSource:=(@current_homotopy_source_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation C:=(fun d=>@current_space R h2 n Full hFull d).
Local Notation Input:=(fun d=>@current_translation_chain_input R h2 n d z).
Local Notation Chain:=(fun d=>@current_translation_chain R h2 n d z).

(** Source for [current_translation_positive_homotopy]:
    tau_z#T−T=boundary(H^z#([0,1] times T))
    +H^z#([0,1] times boundary T), by 4.1.9,
    p. 363, underlying 4.1.18, p. 374. *)
Theorem current_translation_positive_homotopy j (T:C j.+1):
  @current_translation_pushforward R h2 n j.+1 z T-T=
  @current_boundary R h2 n j.+1 Full hFull (Chain j.+1 T)+
    Chain j (@current_boundary R h2 n j Full hFull T).
Proof.
pose P:=Input j.+1 T.
pose hProper:=@current_translation_chain_proper R h2 n j.+1 z T.
pose B:=@current_boundary R h2 n j Full hFull T.
pose PB:=@current_boundary R h2 n j Full hSource P.
pose hPB:=@current_homotopy_boundary_cylinder_proper R h2 n n j
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1 P hProper.
pose hB:=@current_translation_chain_proper R h2 n j z B.
have hInputB:PB=Input j B.
  exact:esym (@current_domain_transport_boundary R h2 n Full hFull Full (erefl _) hSource j T).
have hChainB:=@current_deformation_chain_current_congruence R h2 n n j
  (fun _=>True) Full Full (fun x:X=>x) tau H hH PB (Input j B) hPB hB hInputB.
have hOriginal:=@current_homotopy_positive_formula R h2 n n j
  (fun _=>True) Full Full (fun x:X=>x) tau H hH P hProper.
pose Transport:=@current_domain_transport R h2 n Full hTarget Full (erefl _) hFull j.+1.
have hEqual:=congr1 Transport hOriginal.
rewrite (Bilinear.linB (hom_linear Transport)) (Bilinear.linD (hom_linear Transport)) in hEqual.
rewrite /Transport current_domain_transport_boundary hChainB
  (@current_translation_initial_image R h2 n j.+1 T z)
  (@current_translation_final_image R h2 n j.+1 T z) in hEqual.
exact:hEqual.
Qed.

(** Source for [current_translation_zero_homotopy]: the
    original degree-zero identity has only one
    deformation boundary, by 4.1.9, p. 363,
    underlying 4.1.18, p. 374. *)
Theorem current_translation_zero_homotopy (T:C 0%N):
  @current_translation_pushforward R h2 n 0%N z T-T=
  @current_boundary R h2 n 0%N Full hFull (Chain 0%N T).
Proof.
have hOriginal:=@current_homotopy_zero_formula R h2 n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH (Input 0%N T)
  (@current_translation_chain_proper R h2 n 0%N z T).
pose Transport:=@current_domain_transport R h2 n Full hTarget Full (erefl _) hFull 0%N.
have hEqual:=congr1 Transport hOriginal.
rewrite (Bilinear.linB (hom_linear Transport)) in hEqual.
rewrite /Transport current_domain_transport_boundary
  (@current_translation_initial_image R h2 n 0%N T z)
  (@current_translation_final_image R h2 n 0%N T z) in hEqual.
exact:hEqual.
Qed.
End CurrentTranslationChainHomotopy.
