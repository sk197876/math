(** Federer (1969), 4.1.18, p. 374: the
    fixed-z deformation has mass at most |z| M(T).
    The spatial derivative is the identity, so the
    sharp coefficient is one even in high degree.
    The identity operator is only bounded above by
    one, retaining ambient dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct HomSpaceTopology EuclideanHomOperator
  CurrentDomain CurrentSpaces CurrentMapDifferential CurrentIntegrationCriterion
  CurrentFiniteMassRepresentation CurrentMassSealed CurrentMassBasic
  CurrentAffineConstantWeightBound CurrentSmoothAffineMajorantMassBound
  CurrentEqualDomainQuantities CurrentTranslationHomotopy CurrentTranslationChain
  CurrentTranslations EuclideanAdditiveGroup CurrentAffineHomotopySealed
  CurrentHomotopyUP CurrentHomotopyDomain CurrentDeformationChainSealed
  NormalisedCurrentSealed DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP SummableRealFunctionUP MeasureIntegralUP
  MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentTranslationChainMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(@current_space R h2 n Full hFull m).
Variable z:X.
Local Notation Id:=(hom_of_linear (@linear_id R X)).
Local Notation tau:=(@euclidean_translation R n z).
Local Notation H:=(@current_translation_homotopy R n z).
Local Notation hH:=(@current_translation_homotopy_laws R n z).
Local Notation hSource:=(@current_homotopy_source_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R n n
  (fun _=>True) Full Full (fun x:X=>x) tau H hH.1).
Local Notation Input:=(@current_translation_chain_input R h2 n m z).
Local Notation Chain:=(@current_translation_chain R h2 n m z).
Local Notation Op:=(@euclidean_operator_norm R n n).

(** Source for [current_translation_endpoint_differential_cap]:
    both original endpoint differential norms are at
    most one, by 3.1.1 and 1.7.6, as used
    in the sharp bound of 4.1.18, p. 374. *)
Theorem current_translation_endpoint_differential_cap x:
  Op (@current_map_differential R n n Full (fun y:X=>y) x)<=1 /\
  Op (@current_map_differential R n n Full tau x)<=1.
Proof.
have hBound:norm_bounded_linear NX NX Id.
  exists 1;split;first exact:ler01.
  by move=>v;change (is_true (NX v<=1*NX v));rewrite mul1r.
have hDId:=@norm_differential_linear R X X NX NX hNX hNX Full x Id
  (hFull x Logic.I) hBound.
have hId:@current_map_differential R n n Full (fun y:X=>y) x=Id.
  exact:(@current_map_differential_unique R n n Full (fun y:X=>y) x Id hDId).
have hTau:@current_map_differential R n n Full tau x=Id.
  exact:(@current_map_differential_unique R n n Full tau x Id
    (@current_translation_differential R n z x)).
have hNorm:Op Id<=1.
  apply:hom_operator_norm_least;first exact:ler01.
  by move=>v;change (is_true (NX v<=1*NX v));rewrite mul1r.
rewrite hId hTau;exact:(conj hNorm hNorm).
Qed.

(** Source for [current_translation_chain_finite_mass]:
    M(h_z#([0,1] times T))<=|z| M(T),
    Federer 4.1.18, p. 374, obtained directly
    from 4.1.9's support-wise affine estimate.
    The mass witness is the actual finite mass;
    no normality or compactness is added. *)
Theorem current_translation_chain_finite_mass (T:C) (b:R):
  @CurrentMass.value R h2 n m Full hFull T=b%:E ->
  (@CurrentMass.value R h2 n (1+m)%N Full hFull (Chain T)<=
    ((NX z)*b)%R%:E)%E.
Proof.
move=>hMass.
have hInputMass:@CurrentMass.value R h2 n m Full hSource (Input T)=b%:E.
  by rewrite /current_translation_chain_input current_equal_domain_mass.
have hInputFinite:(@CurrentMass.value R h2 n m Full hSource (Input T)< +oo)%E.
  by rewrite hInputMass ltry.
pose hInput:=@current_finite_mass_representation R h2 n m Full hSource
  (Input T) hInputFinite.
have hAffine:forall t x,(fun _:R=>True) t->Full x->
    @current_homotopy_slice_map R n n H t x=(1-t)*:x+t*:tau x.
  move=>t x _ _;exact:(@CurrentAffineHomotopy.laws R n n (fun y:X=>y) tau t x).
have hBound:=@current_smooth_affine_majorant_mass_bound R h2 n n m
  (fun _=>True) Full Full (fun y:X=>y) tau H hH (Input T) hInput hAffine
  (@current_translation_chain_proper R h2 n m z T) (fun _=>1)
  (fun x _=>(current_translation_endpoint_differential_cap x).1)
  (fun x _=>(current_translation_endpoint_differential_cap x).2).
have hIntegral:=@current_original_variation_bounded_integral R h2 n m Full hSource
  (Input T) hInput b (NX z)
  (fun x:current_domain R n Full=>
    NX (tau (set_val x)-set_val x)*(1:R)^+m)
  hInputMass.
have hConstant:forall x:current_domain R n Full,
    @current_support R h2 n Full hSource m (Input T) (set_val x)->
    NX (tau (set_val x)-set_val x)*(1:R)^+m<=NX z.
  by move=>x _;rewrite /euclidean_translation addrK expr1n mulr1.
have hTotal:=hIntegral hConstant.
rewrite /current_translation_chain current_equal_domain_mass.
exact:le_trans hBound hTotal.
Qed.
End CurrentTranslationChainMass.
