

#use "Examples/reduct.ml";; 


let sort_IND, sort_REC = define_type
	"sort = Kind | Prop"

let term_IND, term_REC = define_type
	"term = Sort sort 
	      | Var num
	      | Abs term term
	      | App term term
  	      | Prod term term"

let env = `term list`

(* check: what is new_recursive_definition *)

let slide = define 
`slide k f i = if i<k then i else f (i-k) + k`

let COND_CONV = 
	RATOR_CONV (LAND_CONV NUM_LT_CONV) THENC
	(REWRITE_CONV [COND_CLAUSES]);;
	  ;;
COND_CONV `if 1 < 2 then 1 else 2`;;

   let th = COND_CLAUSES in 
	(*prove (`! a b. if T then a else b = a /\
                    ! a b. if F then a else b = b,
                    REWRITE_TAC []) in *)



let SLIDE_CONV = 
	(REWRITE_CONV [slide]) 
	THENC COND_CONV THENC NUM_REDUCE_CONV;;
   
SLIDE_CONV `slide 2 (\ i. i + 3) 1`;;
SLIDE_CONV `slide 2 (\i. i + 4) 7`;;

(*
g `! k g f i. slide k g (slide k f i) = slide k (g o f) i`;;
  
e (REPEAT STRIP_TAC THEN SIMP_TAC [slide; o_DEF; FUN_EQ_THM]);;
e (COND_CASES_TAC);;

(* 1/2 *)
e (COND_CASES_TAC);;

e (SIMP_TAC[]);;

e (ASM_ARITH_TAC);;

(* 2/2 *)
e (COND_CASES_TAC);;

e (ASM_ARITH_TAC);;

e (SIMP_TAC [] THEN ASM_MESON_TAC [ADD_SUB]);;
*)

let slide_slide = prove
(`! k g f i. slide k g (slide k f i) = slide k (g o f) i`,
  REPEAT STRIP_TAC THEN SIMP_TAC [slide; o_DEF; FUN_EQ_THM] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THENL
  [SIMP_TAC []; ASM_ARITH_TAC; ASM_ARITH_TAC;
    SIMP_TAC [] THEN ASM_MESON_TAC [ADD_SUB]]);;



let slide_id = prove
(`!k. slide k (\ i. i) = \ i. i`,
  STRIP_TAC THEN SIMP_TAC [slide; FUN_EQ_THM] THEN STRIP_TAC
    THEN COND_CASES_TAC THENL [REFL_TAC; ASM_ARITH_TAC]);;


let tmlift = define 
`tmlift f (Sort s) = Sort s /\
 tmlift f (Var i) = Var (f i) /\
 tmlift f (App x y) = App (tmlift f x) (tmlift f y) /\
 tmlift f (Abs x y) = Abs (tmlift f x) (tmlift (slide 1 f) y) /\
 tmlift f (Prod x y) = Prod (tmlift f x) (tmlift (slide 1 f) y)`;;

let TMLIFT_CONV = 
	 
	(REWRITE_CONV [tmlift]) THENC
	(REDEPTH_CONV SLIDE_CONV) THENC NUM_REDUCE_CONV;;

REDEPTH_CONV SLIDE_CONV `Abs (Var 7) (Var (slide 1 (\i. i + 3) 1))`;;


TMLIFT_CONV `tmlift (\i. i + 4) (App (tmlift (\i. i + 2) (Var 2)) (Var 1))`;;
TMLIFT_CONV `tmlift (\i. i + 4) (Abs (tmlift (\i. i + 2) (Var 2)) (Var 1))`;;

let tmlift_id = prove
(`! t. tmlift (\i. i) t = t`,
  MATCH_MP_TAC term_IND THEN 
          SIMP_TAC [tmlift; slide_id]);;

let tmlift_tmlift = prove 
(`! x f g . tmlift f (tmlift g x) = tmlift (f o g) x`,
  MATCH_MP_TAC term_IND THEN
   SIMP_TAC [tmlift; slide_slide; o_DEF; ETA_AX]);;

let tmshift = define
`tmshift k = tmlift (\ i. i+k)`;;

let TMSHIFT_CONV = 
	ONCE_REWRITE_CONV [tmshift] THENC
	TMLIFT_CONV;;

TMSHIFT_CONV `tmshift 3 (App (tmlift (\i. i + 2) (Var 2)) (Var 1))`;;
TMSHIFT_CONV `tmshift 3 (Abs (tmlift (\i. i + 2) (Var 2)) (Var 1))`;;

let tmshift_tmshift = prove
(`!k j x. tmshift k (tmshift j x) = tmshift (j+k) x`,
  SIMP_TAC [tmshift] THEN REWRITE_TAC [tmlift_tmlift; o_DEF] THEN
  REPEAT STRIP_TAC THEN 
  REWRITE_TAC [ADD_ASSOC] THEN REFL_TAC);;

let tmpush = define
`tmpush k f i = (if i < k then Var i else tmshift k (f (i - k)))`;;

let TMPUSH_CONV = 
	REWRITE_CONV [tmpush] THENC
	COND_CONV THENC 
	TRY_CONV TMSHIFT_CONV;;
TMPUSH_CONV `tmpush 2 (\i. Var (i + 3)) 5`;;
TMPUSH_CONV `tmpush 2 (\i. Var 27) 1`;;



(* tmpush k is injective *)
let tmpush_inj = prove
(`! k f g. (! i. f i = g i) ==> tmpush k f = tmpush k g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FUN_EQ_THM; tmpush]);;

let tmpush_ref = prove
(`! k. tmpush k Var = Var`,
  SIMP_TAC [tmpush; FUN_EQ_THM; tmshift; tmlift] THEN REPEAT STRIP_TAC THEN 
   COND_CASES_TAC THEN REWRITE_TAC [injectivity "term"] THEN ASM_ARITH_TAC);;
(*
let trivial_arith = prove
(`! k x. x + k < k <=> F`, ARITH_TAC);;
*)


let slide_inj = prove
(`! k f g. (!i. f i = g i) ==> slide k f = slide k g`,
  SIMP_TAC [FUN_EQ_THM; slide]);;

(* needs the same for slide *)
let tmlift_inj_helper = prove
(`! x f g. (! i. f i = g i) ==> tmlift f x = tmlift g x`,
  MATCH_MP_TAC term_IND THEN SIMP_TAC [tmlift] THEN REPEAT STRIP_TAC
  THEN ASM_SIMP_TAC [injectivity "term"; slide_inj] THEN 
  ASM_MESON_TAC [slide_inj]);;

let tmlift_inj = prove
(`! f g . (!i. f i = g i) ==> tmlift f = tmlift g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FUN_EQ_THM]
  THEN STRIP_TAC THEN MATCH_MP_TAC tmlift_inj_helper THEN ASM_MESON_TAC[]);;


(* tmpush_tmlift *)
let tmpush_tmlift = prove
(`! k g f. tmpush k ((tmlift g) o f) = tmlift (slide k g) o tmpush k f`,
  REPEAT STRIP_TAC THEN SIMP_TAC [tmpush; tmlift; o_DEF; FUN_EQ_THM]
  THEN STRIP_TAC THEN COND_CASES_TAC THEN 
  ASM_SIMP_TAC[tmlift; slide; tmshift; tmlift_tmlift; o_DEF] THEN 
  MATCH_MP_TAC tmlift_inj_helper THEN SIMP_TAC [ADD_SUB] THEN STRIP_TAC
  THEN ASM_ARITH_TAC);;

let tmbind = define 
`tmbind f (Sort a) = Sort a /\
 tmbind f (Var i) = f i /\
 tmbind f (App x y) = App (tmbind f x) (tmbind f y) /\
 tmbind f (Abs x y) = Abs (tmbind f x) (tmbind (tmpush 1 f) y) /\
 tmbind f (Prod x y) = Prod (tmbind f x) (tmbind (tmpush 1 f) y)`;;

let TMBIND_CONV =
	ONCE_REWRITE_CONV [tmbind] THENC 
	REDEPTH_CONV TMPUSH_CONV;; THENC
	TRY_CONV TMLIFT_CONV THENC
	REDEPTH_CONV COND_CONV;;
	REPEATC (CHANGED_CONV( 
	ONCE_REWRITE_CONV [tmbind] THENC 
	(TRY_CONV TMPUSH_CONV) THENC
	TRY_CONV COND_CONV))
		;;

let TMBIND_CONVS = REDEPTH_CONV TMBIND_CONV;;

TMBIND_CONV `tmbind (\ i. if i < 5 then Sort Prop else Var (i + 2)) 
                 (App (tmlift (\i. i + 2) (Var 2)) (Var 1))`;;
TMBIND_CONVS `tmbind (\ i. if i < 5 then Sort Prop else Var (i + 2)) 
                 (Abs (tmlift (\i. i + 2) (Var 2)) (Var 1))`;;


(* termbind injective *)
let tmbind_inj_helper = prove
(`! x f g . (! i . f i = g i) ==> tmbind f x = tmbind g x`,
  MATCH_MP_TAC term_IND THEN SIMP_TAC [tmbind] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [injectivity "term"; tmpush_inj] THEN ASM_MESON_TAC [tmpush_inj]);;

let tmbind_inj = prove
(`! f g . (!i. f i = g i) ==> tmbind f = tmbind g`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FUN_EQ_THM]
  THEN STRIP_TAC THEN MATCH_MP_TAC tmbind_inj_helper THEN ASM_MESON_TAC[]);;

(*
(* tmlift preserves injectivity *)
g `! f . (! i j. f i = f j ==> i = j) ==> 
        (! x y. tmlift f x = tmlift f y ==> x = y)`;;
e (STRIP_TAC THEN STRIP_TAC);;
e (MATCH_MP_TAC term_IND THEN STRIP_TAC);;
e (
*)
(* tmlift_eq_tmbind *)
let tmlift_eq_tmbind_helper = prove
(`! x f . tmlift f x = tmbind (Var o f) x`,
  MATCH_MP_TAC term_IND THEN SIMP_TAC [tmbind; tmlift; o_DEF; injectivity "term"] 
  THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC tmbind_inj_helper THEN STRIP_TAC THEN 
  ASM_SIMP_TAC [slide; tmpush] THEN COND_CASES_TAC THEN 
  SIMP_TAC[tmshift; tmlift]);;


(* tmlift_eq_tmbind *)  (*  and again the indhyp is not strong enough  *)
                        (*  helper before  *)
let tmlift_eq_tmbind = prove
(`! f. tmlift f = tmbind (Var o f)`,
  STRIP_TAC THEN SIMP_TAC [FUN_EQ_THM] THEN STRIP_TAC THEN
   MESON_TAC [tmlift_eq_tmbind_helper]);;


(* tmlift_tmbind *)
let tmlift_tmbind = prove
(`!t f g. tmlift g (tmbind f t) = tmbind (tmlift g o f) t`,
  MATCH_MP_TAC term_IND THEN
  SIMP_TAC [tmlift; tmbind; o_DEF; injectivity "term"; tmpush_tmlift]);;


(* tmbind_tmlift *)
let tmbind_tmlift = prove
(`! t f g. tmbind g (tmlift f t) = tmbind (g o f) t`,
  MATCH_MP_TAC term_IND THEN
  SIMP_TAC [tmlift; tmbind; o_DEF; injectivity "term"]
  THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC tmbind_inj_helper THEN STRIP_TAC THEN SIMP_TAC [tmpush; tmshift; slide] THEN
  REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN ASM_SIMP_TAC[ARITH; ADD_SUB; tmlift_inj_helper]
  THEN ASM_ARITH_TAC THEN ASM_MESON_TAC []);;



(* tmshift_tmbind *)
(*
g `! t m f. tmshift m (tmbind f t) = tmbind (tmshift m o f) t`;;
e (MATCH_MP_TAC term_IND THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [tmshift; tmbind; tmlift; o_DEF; injectivity "term"; tmpush_tmlift;
                 tmlift_tmbind]
   THEN MATCH_MP_TAC tmbind_inj_helper);;
(* 1/2 *)
e (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [tmlift; tmpush]);;
(* 2/2 *)
e (COND_CASES_TAC THEN ASM_SIMP_TAC [tmlift; slide;tmshift;tmlift_tmlift]);;
e (MATCH_MP_TAC tmlift_inj_helper THEN STRIP_TAC THEN ASM_SIMP_TAC [slide; o_DEF; ARITH]
   THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;


e (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [tmlift; tmpush]);;
*)

(*
let tmshift_tmbind = prove 
(`! t m f. tmshift m (tmbind f t) = tmbind (tmshift m o f) t`, 
  MATCH_MP_TAC term_IND THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC [tmshift; tmbind; tmlift; o_DEF; injectivity "term"; 
                tmpush_tmlift; tmlift_tmbind]
  THEN MATCH_MP_TAC tmbind_inj_helper THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [tmlift; tmpush] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC [tmlift; slide;tmshift;tmlift_tmlift] 
  THEN MATCH_MP_TAC tmlift_inj_helper THEN STRIP_TAC THEN 
  ASM_SIMP_TAC [slide; o_DEF; ARITH] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;
*)

let tmshift_tmbind = prove
(`! t m f. tmshift m (tmbind f t) = tmbind (tmshift m o f) t`,
  REWRITE_TAC [tmshift] THEN MESON_TAC [tmlift_tmbind]);;

(* tmbind_tmshift *)
let tmbind_tmshift = prove
(`!k t g. tmbind g (tmshift k t) = tmbind (g o \i. i + k) t`,
  REWRITE_TAC [tmshift] THEN MESON_TAC [tmbind_tmlift]);;

(* tmbind_tmpush_tmpush *)
let tmbind_tmpush_tmpush = prove
(`! k f i. tmbind (tmpush k g) (tmpush k f i) = tmpush k (\ t. tmbind g (f t)) i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC [tmbind; tmpush] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC
  [tmbind; tmpush; tmshift_tmbind;tmshift; o_DEF;tmbind_tmlift] THEN
  MATCH_MP_TAC tmbind_inj_helper THEN GEN_TAC THEN 
  ASM_SIMP_TAC [tmpush; tmlift; o_DEF] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]
  THENL [ASM_ARITH_TAC; ASM_MESON_TAC [ADD_SUB; tmshift] ]);;


(* tmbind_tmbind *)
let tmbind_tmbind = prove 
(`! t f g . tmbind g (tmbind f t) = tmbind (\ u . tmbind g (f u)) t`,
  MATCH_MP_TAC term_IND THEN
  SIMP_TAC [tmbind; injectivity "term"; tmbind_tmpush_tmpush] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC tmbind_inj_helper THEN 
          GEN_TAC THEN SIMP_TAC []);;


(* a helper for ref_tmbind *)
(*
let ref_tmbind_helping_hand = prove
(`! a. tmbind Var a = a ==> tmbind (tmpush 1 Var ) a = a`,
  MATCH_MP_TAC term_IND THEN SIMP_TAC [tmbind; injectivity "term"; tmpush_ref]);;
*)

(* ref_tmbind *)
let ref_tmbind = prove
(`! t. tmbind Var t = t`,
  MATCH_MP_TAC term_IND THEN SIMP_TAC [tmbind; injectivity "term"; tmpush_ref]);;


let tmsubst_rec = define 
`tmsubst_rec n m k = tmbind (\ i. if i = k then n else Var i) m`;;

(* tmsubst_rec is the identity on variables other than the interesting one *)
let tmsubst_rec_on_other_vars = prove
(`! i k. ~(i = k) ==> tmsubst_rec n (Var i) k = Var i`,
  SIMP_TAC [ARITH; tmsubst_rec; tmbind]);;

let tmsubst_rec_on_spec_var = prove
(`! k. tmsubst_rec n (Var k) k = n`,
  SIMP_TAC [tmsubst_rec; tmbind]);;

let tmsubst = define
`tmsubst n m = tmsubst_rec n m 0`;;

let red1_RULES, red1_IND, red1_CASES = new_inductive_definition
`(! m n t. red1 (App (Abs t m) n) (tmsubst n m)) /\
 (! m p n: term. red1 m p ==> red1 (Abs m n) (Abs p n)) /\
 (! m p n: term. red1 m p ==> red1 (Abs n m) (Abs n p)) /\
 (! ml n m: term. red1 ml n ==> red1 (App ml m) (App n m)) /\
 (! m n ml: term. red1 m n ==> red1 (App ml m) (App ml n)) /\
 (! ml n m: term. red1 ml n ==> red1 (Prod ml m) (Prod n m)) /\
 (! m n ml: term. red1 m n ==> red1 (Prod ml m) (Prod ml n))`;;

g `! m n p q. red1 (Abs m n) (Abs p q) <=> (red1 m p /\ n = q \/ red1 n q /\ m = p)`;;
e (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [red1_CASES] THEN 
   REWRITE_TAC [injectivity "term"; distinctness "term"] THEN MESON_TAC []);;

g `! m n p q. ~ (red1 (Abs m n) (App p q))`;;
e (REPEAT GEN_TAC);;
e (ONCE_REWRITE_TAC [red1_CASES]);;
e (SIMP_TAC [distinctness "term"]);;


let red_RULES, red_IND, red_CASES = new_inductive_definition
`(! m: term. red m m) /\
 (! m n p: term. red m n /\ red1 n p ==> red m p)`;;

let red1_imp_red = prove
 (`! m n. red1 m n ==> red m n`,
   MESON_TAC [red1_RULES; red_RULES]);;

let conv_RULES, conv_IND, conv_CASES = new_inductive_definition
`(! m:term. conv m m) /\
 (! m n p:term. conv m n /\ red1 n p ==> conv m p) /\
 (! m n p:term. conv m n /\ red1 p n ==> conv m p)`;;


(*   strong normalization   *)
let acc_RULES, acc_IND, acc_CASES = new_inductive_definition
`! r x. (! y . r y x ==> acc r y) ==> acc r x`;;

let sn = define 
`sn = acc (INV red1)`;;

let normal = define
`normal t <=> ! u. ~(red1 t u)`;;

(* what is an environment *)
(* to each free var. we associate a type, must hence be of type num -> term *)

new_type_abbrev ("env", `:num->term`);;

let empty = define
`empty = \ i . Var i`;;



(* something to push a new element in the env *)


(* there should be an append operation on envs *)
(* we need to lift the free vars in the shifted terms by one *)
let tmbump = define
`tmbump = tmshift 1`;;

let env_append = define
`env_append f tm = \ i. if i = 0 then tmbump tm else tmbump (f (i - 1))`;;
(*
let stupid_helper = prove
(`~ (Var 0 = tmbump (Var 0))`,
  SIMP_TAC [tmbump; tmshift; tmlift; injectivity "term"; ARITH]);;
g `! e v.  ~ (env_append e v = empty)`
e (SIMP_TAC [env_append; empty; FUN_EQ_THM]);;
e (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [NOT_FORALL_THM]);;
e (REPEAT GEN_TAC THEN MESON_TAC [stupid_helper]);;
e (REPEAT GEN_TAC THEN COND_CASES_TAC);;
*)
(* we define at the same time 
	wellformedness wf : env -> bool
	typing tmtype : env -> term -> term -> bool *)

let wf_ty_RULES, wf_ty_IND, wf_ty_CASES = new_inductive_definition
`(wf empty) /\ 
 (! e t a. tmtype e t (Sort a) ==> wf (env_append e t)) /\
 (! e. wf e ==> tmtype e (Sort Prop) (Sort Kind)) /\
 (! e t s1 m u s2. tmtype e t (Sort s1) /\ 
    tmtype (env_append e t) m u /\ tmtype (env_append e t) u (Sort s2)
           ==> tmtype e (Abs t m) (Prod t u) ) /\
 (! e v p u t. tmtype e v p /\ tmtype e u (Prod p t) ==> 
     tmtype e (App u v) (tmsubst v t)) /\
 (! e t s1 u s2. tmtype e t (Sort s1) /\ 
     tmtype (env_append e t) u (Sort s2) 
         ==> tmtype e (Prod t u) (Sort s2)) /\
 (! e m u v s. tmtype e m u /\ tmtype e v (Sort s) /\ conv u v
              ==> tmtype e m v)`;;
 
let ty_CASES = CONJUNCT2 wf_ty_CASES;;
let wf_CASES = CONJUNCT1 wf_ty_CASES;;

(* inversion lemmata *)
(*

g `! e t. wf (env_append e t) ==> wf e`;;
e (REPEAT GEN_TAC);;
e (GEN_REWRITE_TAC LAND_CONV [wf_CASES]);;
e (REPEAT STRIP_TAC);;

g `! e m t. tmtyp e m t ==> tmtyp (env_append e t) m t`;;

g `! e m t. tmtyp e m t ==> wf e`;;
e (REPEAT GEN_TAC);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [ty_CASES]);;
e (GEN_REWRITE_TAC LAND_CONV [ty_CASES]);;
e (DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [ty_CASES]));;
e (ONCE_REWRITE_TAC [ty_CASES]);;
*)
(*
prove_inductive_relations_exist
*)
(* transitivity of red *)
(*
g `! n p. red n p ==> (!m. red m n ==> red m p)`;;
e (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC term_IND THEN REPEAT STRIP_TAC);;
e (SIMP_TAC [red_RULES; red1_RULES]);;
*)




