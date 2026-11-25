(** Federer (1969), 3.2.38, p. 275: the complete finite
    normalized Steiner sum has one uniform error of order 1/v. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import GridSteinerLowerTermBound GridSteinerTopTermBound GridInflationPowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grid_steiner_polynomial_bound]: supporting the
    corrected first display and xi/v conclusion of Federer 3.2.38,
    p. 275. Every index j=0,...,n is retained. The high coefficients
    vanish, the top coefficient is the actual Jacobian times source
    volume, and all lower coefficients have proved uniform caps.
    The upper coefficient c_m is harmlessly included in the error
    constant. This finite algebra assumes no geometric conclusion. *)
Lemma grid_steiner_polynomial_bound (R:realType) m n (hmn:(m<=n)%N)
    (v r J M:R) (b c:'I_n.+1->R):
  1<=v ->0<r ->0<=J ->J<=M ->(forall i,0<=c i) ->
  (forall i:'I_n.+1,(m<i)%N ->b i=0) ->
  b (Ordinal (leq_ltn_trans hmn (ltnSn n)))=J*(v*r)^+m ->
  (forall i:'I_n.+1,(i<m)%N ->b i<=c i*(v*r)^+i) ->
  (\sum_(i:'I_n.+1) b i*((1+m%:R/v)*r)^+(n-i))/r^+(n-m)<=
    J*(v*r)^+m+
      (((1+m%:R)^+n*(\sum_i c i)+
        M* m%:R*(\sum_(i<n-m) (1+m%:R)^+i))/v)*(v*r)^+m.
Proof.
move=>hv1 hr hJ hJM hc hHigh hTop hLow.
pose iM:'I_n.+1:=Ordinal (leq_ltn_trans hmn (ltnSn n)).
pose A:R:=1+m%:R/v.
pose U:R:=(1+m%:R)^+n.
pose E:R:=m%:R*(\sum_(i<n-m) (1+m%:R)^+i).
pose H:R:=(v*r)^+m.
pose q (i:'I_n.+1):R:=b i*(A*r)^+(n-i)/r^+(n-m).
pose T:R:=J*H+(M*E/v)*H.
have hv:0<v:=lt_le_trans ltr01 hv1.
have hA:0<=A by apply:addr_ge0; [exact:ler01|apply:divr_ge0; [exact:ler0n|exact:ltW hv]].
have hU:0<=U:=exprn_ge0 _ (addr_ge0 ler01 (ler0n R m)).
have hH:0<=H:=exprn_ge0 _ (mulr_ge0 (ltW hv) (ltW hr)).
have hE:0<=E.
  apply:mulr_ge0; first exact:ler0n.
  apply:sumr_ge0=>i _; exact:exprn_ge0 _ (addr_ge0 ler01 (ler0n R m)).
have hInflation:A^+(n-m)<=1+E/v.
  exact:(@grid_inflation_power_increment_bound R v m (n-m) hv1).
have hTopBound:q iM<=T.
  rewrite /q /iM hTop.
  exact:(@grid_steiner_top_term_bound R v r A J M E m n hv hr hJ hJM hE hmn hInflation).
have hCostNonnegative i:0<=c i*H*U/v.
  apply:divr_ge0; last exact:ltW hv.
  exact:mulr_ge0 (mulr_ge0 (hc i) hH) hU.
have hRemainder i:i!=iM ->q i<=c i*H*U/v.
  move=>hNe; case:(ltngtP (i:nat) m)=>[hlt|hgt|heq].
  - exact (@grid_steiner_lower_term_bound R v r A U (b i) (c i) i m n
      hv1 hr hA (hc i) hlt hmn
      (@grid_inflation_power_upper_bound R v m (n-i) n hv1 (leq_subr i n)) (hLow i hlt)).
  - rewrite /q (hHigh i hgt) !mul0r; exact:hCostNonnegative.
  - have hIndex:i=iM by apply:val_inj; exact heq.
    by rewrite hIndex eqxx in hNe.
have hPoint i:q i<=(if i==iM then T else 0)+c i*(H*U/v).
  case:(eqVneq i iM)=>[->|hNe].
  - apply:le_trans hTopBound _.
    have hNonnegative:0<=c iM*(H*U/v).
      have hIdentity:c iM*(H*U/v)=c iM*H*U/v by ring.
      by rewrite hIdentity.
    by rewrite lerDl.
  - rewrite add0r.
    have hIdentity:c i*(H*U/v)=c i*H*U/v by ring.
    rewrite hIdentity; exact:hRemainder i hNe.
have hSum:(\sum_i q i)<=\sum_i ((if i==iM then T else 0)+c i*(H*U/v)).
  apply:ler_sum=>i _; exact:hPoint.
have hIndicator:(\sum_(i:'I_n.+1) (if i==iM then T else 0))=T.
  rewrite (bigD1 iM) //= eqxx big1 ?addr0 //.
  move=>i hi; by rewrite (negbTE hi).
have hRemainderSum:(\sum_i c i*(H*U/v))=(\sum_i c i)*(H*U/v).
  by rewrite mulr_suml.
rewrite big_split hIndicator hRemainderSum in hSum.
have hExplicit:(\sum_i q i)<=T+(\sum_i c i)*(H*U/v).
  exact hSum.
have hAlgebra:T+(\sum_i c i)*(H*U/v)=
    J*H+((U*(\sum_i c i)+M*E)/v)*H by rewrite /T; ring.
rewrite hAlgebra /q -mulr_suml /A /H /U /E !mulrA in hExplicit.
exact hExplicit.
Qed.
