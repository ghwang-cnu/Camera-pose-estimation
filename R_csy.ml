needs "Multivariate/transcendentals.ml";;
needs "Multivariate/cross.ml";;
needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* More properties of sin, cos function.                                     *)
(* ------------------------------------------------------------------------- *)   

let SIN_CONVERGES = prove
    (`!a. ((\n. --(&1) pow n * a pow (2 * n + 1) / &(FACT(2 * n + 1)))
            real_sums sin(a)) (from 0)`, 
    let th1 = SPECL [`Cx a`] CSIN_CONVERGES in
    GEN_TAC THEN MP_TAC th1 THEN 
    SIMP_TAC[GSYM CX_NEG;GSYM CX_POW;GSYM CX_MUL;GSYM CX_DIV;GSYM CX_SIN] THEN
    SIMP_TAC[GSYM o_DEF; GSYM REAL_SUMS_COMPLEX]);;
    
let SIN_CONVERGES_UNIQUE = prove
    (`!w a. ((\n. --(&1) pow n * a pow (2 * n + 1) / &(FACT(2 * n + 1)))
            real_sums w) (from 0)
                    <=> w = sin(a)`,
    REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[SIN_CONVERGES] THEN
    DISCH_THEN(MP_TAC o C CONJ (SPEC `a:real` SIN_CONVERGES)) THEN
    REWRITE_TAC[REAL_SERIES_UNIQUE]);;
  
let SIN_EQ_REAL_INFSUM = prove
    (`!a. (real_infsum (from 0) 
     (\n. --(&1) pow n * a pow (2 * n + 1) / &(FACT(2 * n + 1)))) = sin(a)`,
    STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN SIMP_TAC[SIN_CONVERGES]);;

let COS_CONVERGES = prove
    (`!a. ((\n. --(&1) pow n * a pow (2 * n) / &(FACT(2 * n)))
            real_sums cos(a)) (from 0)`, 
    let th1 = SPECL [`Cx a`] CCOS_CONVERGES in
    GEN_TAC THEN MP_TAC th1 THEN 
    SIMP_TAC[GSYM CX_NEG;GSYM CX_POW;GSYM CX_MUL;GSYM CX_DIV;GSYM CX_COS] THEN
    SIMP_TAC[GSYM o_DEF; GSYM REAL_SUMS_COMPLEX]);;
    
let COS_CONVERGES_UNIQUE = prove
    (`!w a. ((\n. --(&1) pow n * a pow (2 * n) / &(FACT(2 * n)))
            real_sums w) (from 0)
                    <=> w = cos(a)`,
    REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[COS_CONVERGES] THEN
    DISCH_THEN(MP_TAC o C CONJ (SPEC `a:real` COS_CONVERGES)) THEN
    REWRITE_TAC[REAL_SERIES_UNIQUE]);;

let COS_EQ_REAL_INFSUM = prove
    (`!a. (real_infsum (from 0) 
     (\n. --(&1) pow n * a pow (2 * n) / &(FACT(2 * n)))) = cos(a)`,
    STRIP_TAC THEN MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN SIMP_TAC[COS_CONVERGES]);;

(* ------------------------------------------------------------------------- *)
(* The relationship of tan, sin, cos function.                               *)
(* ------------------------------------------------------------------------- *)
  
let COS_DOUBLE_TAN = prove
    (`!a:real. ~(cos a = &0) ==> cos (a * &2) = inv (&1 + tan (a) * tan (a)) * (&1 - tan (a) * tan (a))`,
    REWRITE_TAC[GSYM REAL_POW_2;tan;REAL_POW_DIV;GSYM REAL_LT_POW_2] THEN
    REWRITE_TAC[real_div] THEN 
    SIMP_TAC[GSYM (ISPEC `cos a pow 2` REAL_MUL_RINV);REAL_ARITH `&0 < x ==> ~(x = &0)`] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB;GSYM REAL_SUB_RDISTRIB] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[SIN_CIRCLE;REAL_MUL_LID;REAL_MUL_RID;REAL_INV_INV;COS_DOUBLE;GSYM REAL_MUL_ASSOC;REAL_MUL_LINV;REAL_ARITH `&0 < x ==> ~(x = &0)`]);;

let COS_DOUBLE_TAN_ALT = prove    
    (`!a:real. ~(cos a = &0) ==> &1 - cos (a * &2) = inv (&1 + tan (a) * tan (a)) * (&2 * tan (a) * tan (a))`,
    let lem = prove 
    (`!a. inv (&1 + tan a * tan a) * (&1 + tan a * tan a) = &1`,
    GEN_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    SIMP_TAC[REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`;REAL_LE_SQUARE]) in 
    let lem1 = MESON [lem] `!a. &1 - inv (&1 + tan a * tan a) * (&1 - tan a * tan a) = inv (&1 + tan a * tan a) * (&1 + tan a * tan a) - inv (&1 + tan a * tan a) * (&1 - tan a * tan a)` in 
    SIMP_TAC[COS_DOUBLE_TAN;lem1;GSYM REAL_SUB_LDISTRIB] THEN
    REAL_ARITH_TAC);;
    
let SIN_DOUBLE_TAN = prove
    (`!a:real. ~(cos a = &0) ==> sin (a * &2) = inv (&1 + tan (a) * tan (a)) * (&2 * tan (a))`,
    REWRITE_TAC[GSYM REAL_POW_2;tan;REAL_POW_DIV;GSYM REAL_LT_POW_2] THEN
    REWRITE_TAC[real_div] THEN 
    SIMP_TAC[GSYM (ISPEC `cos a pow 2` REAL_MUL_RINV);REAL_ARITH `&0 < x ==> ~(x = &0)`] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[SIN_CIRCLE;REAL_MUL_LID;REAL_MUL_RID;REAL_INV_INV;SIN_DOUBLE;GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_POW_2;REAL_LT_SQUARE;REAL_MUL_LINV;REAL_MUL_LID;REAL_ARITH `a * b * c * d * d :real = a * b * (c * d) * d`]);;  
  
(* ------------------------------------------------------------------------- *)
(* The definition and properties of metric on R                              *)
(* ------------------------------------------------------------------------- *)

let real_dist = new_definition
  `real_dist(x,y) = abs(x - y)`;;

let REAL_DIST_REFL = prove
    (`!x. real_dist(x,x) = &0`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_SYM = prove
    (`!x y. real_dist(x,y) = real_dist(y,x)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_POS_LE = prove
    (`!x y. &0 <= real_dist(x,y)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_REAL_ABS_DIST = prove
    (`!x y:real. abs(real_dist(x,y)) = real_dist(x,y)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE = prove
    (`!x:real y z. real_dist(x,z) <= real_dist(x,y) + real_dist(y,z)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE_ALT = prove
    (`!x y z. real_dist(y,z) <= real_dist(x,y) + real_dist(x,z)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_EQ_0 = prove
    (`!x y. (real_dist(x,y) = &0) <=> (x = y)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_POS_LT = prove
    (`!x y. ~(x = y) ==> &0 < real_dist(x,y)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_NZ = prove
    (`!x y. ~(x = y) <=> &0 < real_dist(x,y)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE_LE = prove
    (`!x y z e. real_dist(x,z) + real_dist(y,z) <= e ==> real_dist(x,y) <= e`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE_LT = prove
    (`!x y z e. real_dist(x,z) + real_dist(y,z) < e ==> real_dist(x,y) < e`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE_HALF_L = prove
    (`!x1 x2 y. real_dist(x1,y) < e / &2 /\ real_dist(x2,y) < e / &2 ==> real_dist(x1,x2) < e`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE_HALF_R = prove
    (`!x1 x2 y. real_dist(y,x1) < e / &2 /\ real_dist(y,x2) < e / &2 ==> real_dist(x1,x2) < e`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_TRIANGLE_ADD = prove
    (`!x x' y y'. real_dist(x + y,x' + y') <= real_dist(x,x') + real_dist(y,y')`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_MUL = prove
    (`!x y c. real_dist(c * x,c * y) = abs(c) * real_dist(x,y)`,
    SIMP_TAC[real_dist;GSYM REAL_SUB_LDISTRIB;REAL_ABS_MUL]);;

let REAL_DIST_TRIANGLE_ADD_HALF = prove
    (`!x x' y y':real. real_dist(x,x') < e / &2 /\ real_dist(y,y') < e / &2 ==> real_dist(x + y,x' + y') < e`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_LE_0 = prove
    (`!x y. real_dist(x,y) <= &0 <=> x = y`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;

let REAL_DIST_EQ = prove
    (`!w x y z. real_dist(w,x) = real_dist(y,z) <=> real_dist(w,x) pow 2 = real_dist(y,z) pow 2`,
    REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[REAL_POW_2];ALL_TAC] THEN
    MESON_TAC[REAL_DIST_POS_LE;ARITH_RULE `~(2 = 0)`;REAL_POW_EQ]);;

let REAL_DIST_0 = prove
    (`!x. real_dist(x,&0) = abs(x) /\ real_dist(&0,x) = abs(x)`,
    SIMP_TAC[real_dist] THEN CONV_TAC REAL_FIELD);;
  
let euclideanreal_metric = new_definition
    `euclideanreal_metric = metric ((:real), real_dist)`;;
  
let EUCLIDEANREAL_METRIC = prove
    (`mdist (euclideanreal_metric:(real)metric) = real_dist /\
        mspace euclideanreal_metric = (:real)`,
    SUBGOAL_THEN `is_metric_space ((:real),real_dist)` MP_TAC THENL
    [REWRITE_TAC[is_metric_space; IN_UNIV; REAL_DIST_POS_LE; REAL_DIST_EQ_0;
                 REAL_DIST_SYM; REAL_DIST_TRIANGLE];
     SIMP_TAC[euclideanreal_metric; MDIST; MSPACE]]);;

let OPEN_IN_EUCLIDEANREAL_METRIC = prove
    (`open_in (mtopology euclideanreal_metric) = real_open:(real->bool)->bool`,
    REWRITE_TAC[FUN_EQ_THM; OPEN_IN_MTOPOLOGY; real_open;GSYM real_dist;EUCLIDEANREAL_METRIC;SUBSET_UNIV; SUBSET; IN_MBALL; IN_UNIV; REAL_DIST_SYM]);;
              
let MTOPOLOGY_EUCLIDEANREAL_METRIC = prove
    (`mtopology euclideanreal_metric = euclideanreal:(real)topology`,
    REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_EUCLIDEANREAL_METRIC; REAL_OPEN_IN]);;
    
let LIMIT_EUCLIDEANREAL = prove
    (`!f:A->real x net. limit euclideanreal f x net <=> (f ---> x) net`,
    REWRITE_TAC[LIMIT_METRIC; GSYM MTOPOLOGY_EUCLIDEANREAL_METRIC] THEN
    REWRITE_TAC[EUCLIDEANREAL_METRIC; IN_UNIV; tendsto_real;GSYM real_dist]);;  

(* ------------------------------------------------------------------------- *)
(* The definition and properties of power of matrix                          *)
(* ------------------------------------------------------------------------- *)

let matrix_pow = define
    `((matrix_pow: real^N^N->num->real^N^N) A 0 = (mat 1:real^N^N)) /\ (matrix_pow A (SUC n) = A ** (matrix_pow A n))`;;
    
parse_as_infix("matrix_pow",(200,"right"));;

let MATRIX_POW_1 = prove
    (`!A. A matrix_pow 1 = A`,
     REWRITE_TAC[num_CONV `1`] THEN SIMP_TAC[matrix_pow;MATRIX_MUL_RID]);;

let MATRIX_POW_2 =  prove
    (`! A. A matrix_pow 2 = A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `2`;MATRIX_POW_1]);;
    
let MATRIX_POW_3 =  prove
    (`! A. A matrix_pow 3 = A ** A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `3`;num_CONV `2`;MATRIX_POW_1]);;
     
let MATRIX_POW_0 = prove
    (`!n. (mat 0:real^N^N) matrix_pow SUC n = (mat 0:real^N^N)`,
     SIMP_TAC[matrix_pow;MATRIX_MUL_LZERO]);;

let MATRIX_POW_ONE = prove
    (`!n. (mat 1:real^N^N) matrix_pow n = (mat 1:real^N^N)`,
     INDUCT_TAC THEN ASM_SIMP_TAC [matrix_pow;MATRIX_MUL_LID]);;
    
let MATRIX_POW_ADD = prove
    (`!A m n. A matrix_pow (m + n) = (A matrix_pow m) ** (A matrix_pow n)`,
     GEN_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[matrix_pow; ADD_CLAUSES; MATRIX_MUL_LID] THEN REWRITE_TAC[MATRIX_MUL_ASSOC]);; 
     
let MATRIX_POW_CMUL = prove
    (`!k:real A:real^N^N n:num. (k %% A) matrix_pow n = (k pow n) %% (A matrix_pow n)`,
     GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [SIMP_TAC [matrix_pow; real_pow; GSYM MAT_CMUL;ARITH];
      SIMP_TAC [matrix_pow;real_pow] THEN
      ASM_SIMP_TAC [MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_CMUL_ASSOC]]);;
      
let MATRIX_POW_TRANSP = prove  
    (`!A:real^N^N n:num. (transp A) matrix_pow n  = transp(A matrix_pow n)`,
    let MATRIX_POW_SUC = prove
    ( `!A:real^N^N n:num.A matrix_pow n ** A = A ** A matrix_pow n`,
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;MATRIX_MUL_RID;MATRIX_MUL_LID]
    THEN SIMP_TAC[matrix_pow] THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN 
    SIMP_TAC[MATRIX_MUL_ASSOC] THEN FIRST_ASSUM (SUBST1_TAC o SYM) 
    THEN SIMP_TAC[])  in
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;TRANSP_MAT] THEN
    ASM_SIMP_TAC[matrix_pow;GSYM MATRIX_TRANSP_MUL;MATRIX_POW_SUC]);;

(* ------------------------------------------------------------------------- *)
(* The related properties of matrix and simple automation for 3X3 matrix     *)
(* ------------------------------------------------------------------------- *)    
      
let MAT3_TAC =
    SIMP_TAC[CART_EQ; LAMBDA_BETA; FORALL_3; SUM_3; DIMINDEX_3; VECTOR_3;
             vector_add; vec; dot; cross; orthogonal; basis; DET_3;
             vector_neg; vector_sub; vector_mul;
             matrix_cmul;matrix_neg;matrix_add;matrix_sub;matrix_mul;matrix_vector_mul; vector_matrix_mul;mat;transp;row;column;rows;columns;ARITH] THEN
    REAL_ARITH_TAC;;      
    
let MAT3_RULE tm = prove(tm,MAT3_TAC);;

let MATRIX_SUB_RNEG = prove
    (`!A B:real^N^M. (A - --B) = A + B`,
    SIMP_TAC[matrix_neg; matrix_sub; matrix_add; CART_EQ;LAMBDA_BETA; REAL_SUB_RNEG]);;
           
let MATRIX_SUB_LNEG = prove
    (`!A B:real^N^M. (--A - B) = --(A + B)`,
    SIMP_TAC[matrix_neg; matrix_sub; matrix_add; CART_EQ;LAMBDA_BETA; REAL_SUB_LNEG]);;

let MATRIX_SUB_NEG2 = prove
    (`!A B:real^N^M. (--A - --B) = B - A`,
    SIMP_TAC[matrix_neg; matrix_sub; CART_EQ;LAMBDA_BETA; REAL_SUB_NEG2]);;

let MATRIX_ADD_SUB =prove
    (`!A B:real^N^M.(A + B) - A = B`,
    SIMP_TAC[matrix_add; matrix_sub; CART_EQ;LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let MATRIX_SUB_SUB = prove
    (`!A B:real^N^M.(A - B) - A = --B`,
    SIMP_TAC[matrix_add; matrix_sub; matrix_neg; CART_EQ;LAMBDA_BETA] THEN REAL_ARITH_TAC);;
           
let MATRIX_VECTOR_SUB_COMPONENT = prove
    (`!A B:real^N^M i. (A - B)$i = A$i - B$i`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:M) /\ !A:real^N^M. A$i = A$k`
    CHOOSE_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN 
    ASM_SIMP_TAC[matrix_sub; vector_sub; LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* The definition of the skew-symmetric matrix.                              *)
(* ------------------------------------------------------------------------- *)    

let skew_sym_matrix = new_definition
    `skew_sym_matrix A <=> transp A = -- A`;;

let vec3_2_ssm = new_definition
    `!a:real^3. (vec3_2_ssm:real^3->real^3^3) a =
     vector [vector[&0; --a$3; a$2];
             vector[a$3; &0; --a$1];
             vector[--a$2; a$1; &0]]:real^3^3`;;

let CROSS_SSM = prove
    (`!a b. a cross b = (vec3_2_ssm a) ** b`,
     REWRITE_TAC[vec3_2_ssm] THEN MAT3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The projection matrix and the tranformation: 3d-vector a--> a * transp a                            *)
(* ------------------------------------------------------------------------- *)     

let proj_matrix = new_definition
    `proj_matrix A <=> transp A = A /\ (!n. n > 0 ==> A matrix_pow n = A)`;;

let vec3_vtrans = new_definition
    `!a:real^3.(vec3_vtrans:real^3 ->real^3^3) a=
     vector [vector [a$1*a$1; a$1*a$2; a$1*a$3];
             vector [a$1*a$2; a$2*a$2; a$2*a$3];
             vector [a$1*a$3; a$3*a$2; a$3*a$3]]:real^3^3`;;             

(* ------------------------------------------------------------------------- *)
(* The properties of the skew-symmetric matrix and projection matrix.                              *)
(* ------------------------------------------------------------------------- *)
             
let VEC3_NORM_EQ_1 = prove
    (`!a:real^3. (norm a = &1) <=> (a$1 * a$1 + a$2 * a$2 + a$3 * a$3 = &1)`,
    SIMP_TAC [vector_norm; SQRT_EQ_1] THEN MAT3_TAC);;
    
let VEC3_VTRANS_CMUL = prove
    (`!a:real^3 c:real. vec3_vtrans(c % a) = (c pow 2) %% vec3_vtrans(a)`,
    REWRITE_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;vec3_vtrans;VECTOR_MUL_COMPONENT;MATRIX_CMUL_COMPONENT;REAL_POW_2;REAL_MUL_AC]);;
    
let VEC3_SSM_CMUL = prove
    (`!a:real^3 c:real. vec3_2_ssm(c % a) = c %% vec3_2_ssm(a)`,
    REWRITE_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;vec3_2_ssm;VECTOR_NEG_COMPONENT;VECTOR_MUL_COMPONENT;MATRIX_CMUL_COMPONENT;REAL_POW_2] THEN REAL_ARITH_TAC);;
    
let VEC3_SSM_TRANSP = prove
    (`!w. transp(vec3_2_ssm w) = -- (vec3_2_ssm w)`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;MATRIX_NEG_COMPONENT;VECTOR_NEG_COMPONENT;transp;vec3_2_ssm] THEN ARITH_TAC);;

let VEC3_VTRANS_TRANSP = prove
    (`!a. transp(vec3_vtrans a) = vec3_vtrans a`,
     SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;transp;vec3_vtrans] THEN ARITH_TAC);;
    
let VEC3_2_SSM = prove
    (`!a:real^3. skew_sym_matrix (vec3_2_ssm a)`,
    SIMP_TAC[skew_sym_matrix;VEC3_SSM_TRANSP]);;

let VEC3_VTRANS_SQUARE = prove
     (`!a. norm a = &1 ==> vec3_vtrans a ** vec3_vtrans a = vec3_vtrans a`,
     SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;matrix_mul;vec3_vtrans;SUM_3;NORM_EQ_1;DOT_3] THEN 
     SIMP_TAC[GSYM REAL_MUL_ASSOC] THEN
     ONCE_REWRITE_TAC[REAL_ARITH `(a:real^3)$1 * b *  (a:real^3)$1* c = ((a:real^3)$1 * (a:real^3)$1)* b * c`] THEN
     SIMP_TAC[REAL_ARITH `a + b + c = &1 <=> a = &1 - b - c`] THEN ARITH_TAC);;

let VEC3_VTRANS = prove
    (`!a:real^3. norm a = &1 ==> proj_matrix (vec3_vtrans a)`,
     SIMP_TAC[proj_matrix;VEC3_VTRANS_TRANSP] THEN
     GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [ARITH_TAC;ALL_TAC] THEN
     SIMP_TAC[ARITH_RULE `SUC n > 0 <=> n = 0 \/ n > 0`] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[GSYM (num_CONV `1`);MATRIX_POW_1];ALL_TAC] THEN
     ASM_SIMP_TAC[matrix_pow;VEC3_VTRANS_SQUARE]);;
    
let VEC3_SSM_TRANSP_SUB = prove
    (`!w. transp(mat 1 - vec3_2_ssm w) = mat 1 + vec3_2_ssm w`,
    REWRITE_TAC[VEC3_SSM_TRANSP;TRANSP_MATRIX_SUB;TRANSP_MAT;MATRIX_SUB;MATRIX_NEG_NEG]);;
    
let VEC3_SSM_TRANSP_ADD = prove
    (`!w. transp(mat 1 + vec3_2_ssm w) = mat 1 - vec3_2_ssm w`,
    REWRITE_TAC[VEC3_SSM_TRANSP;TRANSP_MATRIX_ADD;TRANSP_MAT;MATRIX_SUB]);;
    
let SSM_LMUL_EQ_0 = prove
    (`!a:real^3. vec3_2_ssm a ** vec3_vtrans a = mat 0`,
    SIMP_TAC [vec3_2_ssm;vec3_vtrans] THEN MAT3_TAC);;
               
let SSM_RMUL_EQ_0 = prove
    (`!a:real^3. vec3_vtrans a ** vec3_2_ssm a = mat 0`,
    SIMP_TAC [vec3_2_ssm;vec3_vtrans] THEN MAT3_TAC);;

(* ------------------------------------------------------------------------- *)
(* The properties of high order powers of the skew-symmetric matrix.         *)
(* ------------------------------------------------------------------------- *)

let SSM_POW_2 = prove
    (`!a:real^3.norm a = &1 ==> (vec3_2_ssm a) matrix_pow 2 = vec3_vtrans a - (mat 1:real^3^3)`,
    SIMP_TAC [num_CONV `2`; MATRIX_POW_1; matrix_pow] THEN
    SIMP_TAC [VEC3_NORM_EQ_1;vec3_2_ssm;vec3_vtrans] THEN
    MAT3_TAC);;

let SSM_POW_3 = prove
    (`!a:real^3.norm a = &1 ==> (vec3_2_ssm a) matrix_pow 3 = -- vec3_2_ssm a`,
    SIMP_TAC [matrix_pow; num_CONV `3`; SSM_POW_2] THEN
    SIMP_TAC [VEC3_NORM_EQ_1;vec3_2_ssm;vec3_vtrans] THEN
    MAT3_TAC);;    

let SSM_POW_CYCLICITY = prove
    (`!a:real^3 n. (norm a = &1) ==> ((vec3_2_ssm a) matrix_pow (n + 3) = --((vec3_2_ssm a) matrix_pow (n + 1)))`,
    SIMP_TAC[MATRIX_POW_ADD;SSM_POW_3;MATRIX_POW_1;MATRIX_MUL_LNEG;MATRIX_MUL_RNEG]);;

let MATRIX_CMUL_NEG = prove
    (`!A:real^N^M c:real. c %% (-- A) = ((-- &1) * c) %% A`,
    SIMP_TAC[matrix_cmul; matrix_neg; CART_EQ; LAMBDA_BETA] THEN
    REAL_ARITH_TAC);;
    
let EVEN_DIV2 = prove
    (`!n:num. EVEN n ==> ((n DIV 2) * 2 = n)`,
    let lem = ARITH_RULE `~ (2 = 0)` in
    let th = SPECL [`n:num`;`2`] DIVISION in
    let th1 = CONJUNCT1 (MATCH_MP th lem) in
    METIS_TAC [th1;EVEN_MOD;ADD_CLAUSES]);;

let MATRIX_CMUL_IMP = prove
    (`!A:real^N^M x:real y:real. (x=y) ==> (x %% A = y %% A)`,
    SIMP_TAC [matrix_cmul]);;
 
let REAL_POW_IMP = prove
    (`!x y c:real. (x=y) ==> (c pow x = c pow y)`,
    METIS_TAC[real_pow]);;     

let SSM_POW_N = prove
    (`!a n. (norm a = &1) ==> ((vec3_2_ssm a) matrix_pow n =
     (if n = 0 then mat 1
      else if (EVEN n) then
	   (((--(&1)) pow ((n DIV 2) - 1)) %% (vec3_2_ssm (a) ** vec3_2_ssm (a)))
           else (((--(&1)) pow ((n - 1) DIV 2)) %% vec3_2_ssm (a))))`,
    GEN_TAC THEN INDUCT_TAC THENL
     (*proving the first induct -- P(0)*) 
     [SIMP_TAC[matrix_pow]; ALL_TAC] THEN
        (*proving the second induct -- the relationship between P(n+1) and P(n)*)
      ASM_SIMP_TAC[matrix_pow] THEN
      STRIP_TAC THEN COND_CASES_TAC THENL
         (*discussing the if cases, case 1 -- n = 0*)
      [ASM_SIMP_TAC[EVEN;ARITH;DIV_0;real_pow] THEN
       SIMP_TAC[MATRIX_CMUL_LID;MATRIX_MUL_RID]; ALL_TAC] THEN
          (*end of the case 1; case 2 -- EVEN n*)
       COND_CASES_TAC THENL
        [ASM_SIMP_TAC[ARITH;EVEN;NOT_SUC;MATRIX_MUL_LMUL;MATRIX_MUL_RMUL] THEN
         SIMP_TAC[GSYM MATRIX_POW_3] THEN
         ASM_SIMP_TAC[SSM_POW_3;MATRIX_CMUL_NEG;GSYM real_pow] THEN
         MATCH_MP_TAC MATRIX_CMUL_IMP THEN
         MATCH_MP_TAC REAL_POW_IMP THEN
         SIMP_TAC[ARITH_RULE `SUC n = n + 1`;ARITH_RULE `(n + 1) - 1 = n`] THEN
         SUBGOAL_THEN `2 <= n:num` ASSUME_TAC; ALL_TAC] THENL
        (*Introduce a subgoal for cases 2 -- to proving n DIV 2 - 1 + 1 = n DIV 2*)
         [SIMP_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN
          ASM_SIMP_TAC[] THEN
          UNDISCH_TAC `EVEN(n:num)` THEN CONV_TAC CONTRAPOS_CONV THEN
          SIMP_TAC[DE_MORGAN_THM;num_CONV `1`;EVEN]; ALL_TAC; ALL_TAC] THENL
        (*end of the subgoal*)
          [ASM_SIMP_TAC[ARITH_RULE `2<=n ==> n DIV 2 - 1 + 1= n DIV 2`]; ALL_TAC] THEN
           (*end of the case 2; case 3 -- ~ (EVEN n)*)
           ASM_SIMP_TAC [NOT_SUC;EVEN;MATRIX_MUL_LMUL;MATRIX_MUL_RMUL] THEN
           MATCH_MP_TAC MATRIX_CMUL_IMP THEN
           MATCH_MP_TAC REAL_POW_IMP THEN
           ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The properties of multiple summation                                      *)
(* ------------------------------------------------------------------------- *)

let SUM_6 = prove
 (`!t. sum(1..6) t = t(1) + t(2) + t(3) + t(4)+ t(5)+ t(6)`,
  SIMP_TAC[num_CONV `6`;num_CONV `5`;num_CONV `4`; num_CONV `3`; num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]);;
   
let SUM_SUM_DELTA = prove
    (`!s1 s2 a1 a2. sum s1 (\x1. if x1 = a1:A then (sum s2 (\x2. if x2 = a2:A then b else &0)) else &0) 
    = if ((a1 IN s1) /\ (a2 IN s2)) then b else &0`,
    SIMP_TAC [SUM_DELTA] THEN METIS_TAC []);;
  
let SUM_SUM_BOUND_LT_ALL = prove
    (`!s1:A->bool s2:B->bool f b. FINITE s1 /\ ~(s1 = {}) /\ FINITE s2 /\ ~(s2 = {})
              /\ (!x y. x IN s1 /\ y IN s2 ==> f x y < b)
           ==> sum s2 (\y. sum s1 (\x. f x y)) < &(CARD s1) * &(CARD s2) * b`,
    MESON_TAC [SUM_BOUND_LT_ALL;REAL_ARITH `!a b c:real.a * b * c = b * a * c`]);;    
  
let SUM_SUM_BOUND_LT_GEN = prove
    (`!s1:A->bool s2:B->bool f b. FINITE s1 /\ ~(s1 = {}) /\ FINITE s2 /\ ~(s2 = {})
           /\ (!x y. x IN s1 /\ y IN s2 ==> f x y < b / (&(CARD s1) * &(CARD s2)))
           ==> sum s2 (\y. sum s1 (\x. f x y)) < b`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN 
       `b = &(CARD (s1:A->bool)) * &(CARD (s2:B->bool)) *
        (b / (&(CARD s1) * &(CARD s2)))`
    ASSUME_TAC THENL
    [REWRITE_TAC [REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
     MATCH_MP_TAC REAL_DIV_LMUL THEN 
     UNDISCH_TAC `~(s2:B->bool = {})` THEN
     UNDISCH_TAC `~(s1:A->bool = {})` THEN 
     REWRITE_TAC[GSYM IMP_CONJ] THEN CONV_TAC CONTRAPOS_CONV THEN
     ASM_SIMP_TAC[DE_MORGAN_THM; GSYM HAS_SIZE_0; HAS_SIZE; 
                 GSYM REAL_OF_NUM_EQ; REAL_ENTIRE]; ALL_TAC] THEN 
    ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_SUM_BOUND_LT_ALL THEN ASM_SIMP_TAC[]);;
           
(* ------------------------------------------------------------------------- *)
(* The definition and properties of finite sum of matrix                     *)
(* ------------------------------------------------------------------------- *)             

let msum = new_definition
    `(msum:(A->bool)->(A->real^N^M)->real^N^M) s f = lambda i j. sum s (\x. f(x)$i$j)`;;
  
let MSUM_CLAUSES = prove
    (`(!f. msum {} f = mat 0) /\
        (!x f s. FINITE s
            ==> (msum (x INSERT s) f =
                 if x IN s then msum s f else f(x) + msum s f))`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_CLAUSES] THEN
    SIMP_TAC[MAT_COMPONENT] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_ADD_COMPONENT]);; 
  
let MSUM_EQ_0 = prove
    (`!f s. (!x:A. x IN s ==> (f(x) = mat 0)) ==> (msum s f = mat 0)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; mat] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN SIMP_TAC[SUM_EQ_0]);;
  
let MSUM_0 = prove
    (`msum s (\x. mat 0) = mat 0`,
    SIMP_TAC[MSUM_EQ_0]);;
  
let MSUM_LMUL = prove
    (`!f c s.  msum s (\x. c %% f(x)) = c %% msum s f`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; SUM_LMUL]);;
  
let MSUM_RMUL = prove
    (`!c s v. msum s (\x. c x %% v) = (sum s c) %% v`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; SUM_RMUL]);;

let MSUM_ADD = prove
    (`!f g s. FINITE s ==> (msum s (\x. f x + g x) = msum s f + msum s g)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_ADD]);;

let MSUM_SUB = prove
    (`!f g s. FINITE s ==> (msum s (\x. f x - g x) = msum s f - msum s g)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_SUB_COMPONENT; SUM_SUB]);;

let MSUM_CONST = prove
    (`!c s. FINITE s ==> (msum s (\n. c) = &(CARD s) %% c)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_CONST; MATRIX_CMUL_COMPONENT]);;

let MSUM_COMPONENT = prove
    (`!s f i j. 1 <= i /\ i <= dimindex(:M) /\
                1 <= j /\ j <= dimindex(:N)
            ==> ((msum s (f:A->real^N^M))$i$j = sum s (\x. f(x)$i$j))`,
    SIMP_TAC[msum; LAMBDA_BETA]);;

let MSUM_UNION = prove
    (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
            ==> (msum (s UNION t) f = msum s f + msum t f)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_UNION; MATRIX_ADD_COMPONENT]);;

let MSUM_DELETE = prove
    (`!f s a. FINITE s /\ a IN s
            ==> msum (s DELETE a) f = msum s f - f a`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_DELETE; MATRIX_SUB_COMPONENT]);;

let MSUM_NEG = prove
    (`!f s. msum s (\x. --f x) = --msum s f`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; SUM_NEG; MATRIX_NEG_COMPONENT]);;

let MSUM_EQ = prove
    (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (msum s f = msum s g)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]);;

let MSUM_SUPERSET = prove
    (`!f:A->real^N^M u v.
            u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = mat 0))
            ==> (msum v f = msum u f)`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MAT_COMPONENT] THEN
    ASM_SIMP_TAC[ARITH_RULE `(if k then &0 else &0) = &0`;SUM_SUPERSET]);;

let MSUM_EQ_SUPERSET = prove
    (`!f s t:A->bool.
            FINITE t /\ t SUBSET s /\
            (!x. x IN t ==> (f x = g x)) /\
            (!x. x IN s /\ ~(x IN t) ==> f(x) = mat 0)
            ==> msum s f = msum t g`,
    MESON_TAC[MSUM_SUPERSET; MSUM_EQ]);;

let MSUM_RESTRICT = prove
    (`!f s. msum s (\x. if x IN s then f(x) else mat 0) = msum s f`,
    REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_EQ THEN SIMP_TAC[]);;

let MSUM_CASES = prove
    (`!s P f g. FINITE s
                ==> msum s (\x:A. if P x then (f x):real^N^M else g x) =
                    msum {x | x IN s /\ P x} f + msum {x | x IN s /\ ~P x} g`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; SUM_CASES;
             COND_COMPONENT]);;

let MSUM_SING = prove
    (`!f x. msum {x} f = f(x)`,
    SIMP_TAC[MSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; MATRIX_ADD_RID]);;
  
let MSUM_CLAUSES_NUMSEG = prove
    (`(!m. msum(m..0) f = if m = 0 then f(0) else mat 0) /\
    (!m n. msum(m..SUC n) f = if m <= SUC n then msum(m..n) f + f(SUC n)
                                else msum(m..n) f)`,
    REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[MSUM_SING; MSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; MATRIX_ADD_AC]);;
  
let MSUM_OFFSET = prove
    (`!p f m n. msum(m + p..n + p) f = msum(m..n) (\i. f (i + p))`,
    SIMP_TAC[msum; CART_EQ; LAMBDA_BETA; MAT_COMPONENT; SUM_OFFSET]);;
    
let MSUM_PAIR = prove
    (`!f:num->real^N^M m n.
        msum(2*m..2*n+1) f = msum(m..n) (\i. f(2*i) + f(2*i+1))`,
    SIMP_TAC[CART_EQ; MSUM_COMPONENT; MATRIX_ADD_COMPONENT; SUM_PAIR]);;
             
(* ------------------------------------------------------------------------- *)
(* The properties of trace of transp matrix                                  *)
(* ------------------------------------------------------------------------- *)  

let TRACE_TRANSP_POS_LE = prove
    (`!A:real^N^M. &0 <= trace(transp A ** A)`,
    GEN_TAC THEN SIMP_TAC[trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN SIMP_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC[REAL_LE_SQUARE]);;

let TRACE_TRANSP_SYM = prove
    (`!A:real^N^M B:real^N^M. trace(transp A ** B) = trace(transp B ** A)`,
    METIS_TAC[TRACE_TRANSP; MATRIX_TRANSP_MUL; TRANSP_TRANSP]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of the Frobenius norm of matrix             *)
(* ------------------------------------------------------------------------- *) 

let fnorm = new_definition
    `fnorm A = sqrt(trace(transp A ** A))`;;

let FNORM_REAL = prove
    (`!A:real^1^1. fnorm(A) = abs(A$1$1)`,
    SIMP_TAC[fnorm;trace;transp;matrix_mul;DIMINDEX_1;CART_EQ;LAMBDA_BETA;FORALL_1;SUM_1;ARITH; SUM_SING_NUMSEG;GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

let FNORM_LE = prove
    (`!A:real^N^M B. (fnorm A <= fnorm B) <=> (trace(transp A ** A) <= trace(transp B ** B))`,
    REWRITE_TAC[fnorm] THEN MESON_TAC[SQRT_MONO_LE_EQ; TRACE_TRANSP_POS_LE]);;

let FNORM_LT = prove
    (`!A:real^N^M B. (fnorm A < fnorm B) <=> (trace(transp A ** A) < trace(transp B ** B))`,
    REWRITE_TAC[fnorm] THEN MESON_TAC[SQRT_MONO_LT_EQ; TRACE_TRANSP_POS_LE]);;
  
let FNORM_EQ = prove
    (`!A:real^N^M B. (fnorm A = fnorm B) <=> (trace(transp A ** A) = trace(transp B ** B))`,
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; FNORM_LE]);;
  
let FNORM_0 = prove
    (`fnorm(mat 0) = &0`,
    REWRITE_TAC[fnorm; MATRIX_MUL_RZERO; TRACE_0;SQRT_0]);;      

let FNORM_EQ_0 = prove
    (`!A:real^N^M. fnorm A = &0 <=> A = mat 0`,
    GEN_TAC THEN SIMP_TAC[fnorm;SQRT_EQ_0] THEN
    EQ_TAC THENL
    [SIMP_TAC[trace;transp;matrix_mul;mat;CART_EQ;LAMBDA_BETA] THEN
     SIMP_TAC[ARITH_RULE `(if i = j then &0 else &0) = &0`] THEN
     DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[REAL_ENTIRE] `x * x = &0`)] THEN
     MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN ASM_REWRITE_TAC[REAL_LE_SQUARE] THEN
     UNDISCH_TAC `1 <= i /\ i <= dimindex (:M)` THEN SPEC_TAC (`i:num`,`i:num`) THEN
     MATCH_MP_TAC SUM_POS_EQ_0_NUMSEG THEN
     CONJ_TAC ; ALL_TAC] THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      ASM_REWRITE_TAC[REAL_LE_SQUARE] ; ALL_TAC ; ALL_TAC] THENL
      [ONCE_ASM_SIMP_TAC[GSYM SUM_SWAP_NUMSEG] THEN
       ONCE_ASM_SIMP_TAC[GSYM SUM_SWAP_NUMSEG] THEN
       ASM_SIMP_TAC[] ; ALL_TAC] THEN
       STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_MUL_RZERO;TRACE_0]);;
    
let FNORM_POS_LE = prove
    (`!A:real^N^M. &0 <= fnorm A`,
    GEN_TAC THEN SIMP_TAC[fnorm] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    SIMP_TAC[trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN SIMP_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN SIMP_TAC[REAL_LE_SQUARE]);;

let FNORM_POS_LT = prove
    (`!A:real^N^M. &0 < fnorm A <=> ~(A = mat 0)`,
    MESON_TAC[REAL_LT_LE; FNORM_POS_LE; FNORM_EQ_0]);;

let FNORM_POW_2 = prove
    (`!A:real^N^M. fnorm(A) pow 2 = trace(transp A ** A)`,
    SIMP_TAC[fnorm; SQRT_POW_2; TRACE_TRANSP_POS_LE]);;
    
let FNORM_NEG = prove
    (`!A:real^N^M. fnorm(--A) = fnorm A`,
    REWRITE_TAC[fnorm; TRANSP_MATRIX_NEG; MATRIX_MUL_LNEG; MATRIX_MUL_RNEG; MATRIX_NEG_NEG]);;  

let FNORM_SUB_SYM = prove
    (`!A:real^N^M B:real^N^M. fnorm(A - B) = fnorm(B - A)`,
    MESON_TAC[FNORM_NEG; MATRIX_NEG_SUB]);; 

let FNORM_EQ_0_IMP = prove
    (`!A:real^N^M. (fnorm A = &0) ==> (A = mat 0)`,
    MESON_TAC[FNORM_EQ_0]);;

let FNORM_CAUCHY_SCHWARZ = prove
    (`!A:real^N^M B:real^N^M. trace(transp A ** B) <= fnorm(A) * fnorm(B)`,
    REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC 
     [`fnorm(A:real^N^M) = &0`; `fnorm(B:real^N^M) = &0`] THEN
    ASM_SIMP_TAC[FNORM_EQ_0_IMP; MATRIX_MUL_LZERO; MATRIX_MUL_RZERO;TRANSP_MAT;
                 TRANSP_EQ_0; TRACE_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    MP_TAC(ISPEC `fnorm(A:real^N^M) %% B - fnorm(B:real^N^M) %% A`
           TRACE_TRANSP_POS_LE) THEN
    REWRITE_TAC[TRANSP_MATRIX_SUB;TRANSP_MATRIX_CMUL;
                MATRIX_SUB_LDISTRIB;MATRIX_SUB_RDISTRIB;TRACE_ADD;TRACE_SUB;
                TRACE_CMUL;MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_CMUL_ASSOC] THEN
    SIMP_TAC[GSYM FNORM_POW_2;REAL_POW_2;REAL_LE_REFL] THEN
    REWRITE_TAC[TRACE_TRANSP_SYM; REAL_ARITH
     `&0 <= A * (A * B * B - B * t) - B * (A * t - B * A * A) <=>
      A * B * t <= A * B * A * B`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LE; FNORM_POS_LE]);;

let FNORM_TRIANGLE = prove
    (`!A:real^N^M B:real^N^M. fnorm(A + B) <= fnorm(A) + fnorm(B)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[fnorm] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[GSYM fnorm; TRACE_TRANSP_POS_LE; FNORM_POS_LE; REAL_LE_ADD] THEN
    REWRITE_TAC[TRANSP_MATRIX_ADD;MATRIX_ADD_LDISTRIB;
                MATRIX_ADD_RDISTRIB;TRACE_ADD] THEN
    REWRITE_TAC[REAL_POW_2; GSYM FNORM_POW_2] THEN 
    SIMP_TAC[FNORM_CAUCHY_SCHWARZ; TRACE_TRANSP_SYM;REAL_ARITH
             `t <= A * B ==> (A * A + t) + (t + B * B) <= (A + B) * (A + B)`]);;

let FNORM_EQ_NORM_VECTORIZE = prove
    (`!A:real^N^M. fnorm A = norm(vectorize A)`,
    SIMP_TAC[fnorm;vector_norm;DOT_VECTORIZE]);;
             
let FNORM_SUBMULT = prove
    (`!A:real^N^P B:real^M^N. fnorm (A ** B) <= fnorm (A) * fnorm (B)`,
    SIMP_TAC[FNORM_EQ_NORM_VECTORIZE;NORM_VECTORIZE_MUL_LE]);;
    
let COMPATIBLE_FNORM = prove
    (`!A:real^N^M x. norm (A ** x) <= fnorm (A) * norm x`,
    SIMP_TAC[COMPATIBLE_NORM_VECTORIZE;FNORM_EQ_NORM_VECTORIZE]);;
    
let COMPONENT_LE_FNORM = prove
    (`!A:real^N^M i j. abs(A$i$j) <= fnorm A`,
    let sum_square = prove
    (`!s f:A->real. &0 <= sum s (\x. f(x) * f(x))`,
    METIS_TAC[SUM_POS_LE;REAL_LE_SQUARE]) in
    REPEAT GEN_TAC THEN SUBGOAL_THEN
    `?k1 k2. 1 <= k1 /\ k1 <= dimindex(:M) /\ 1 <= k2 /\ k2 <= dimindex(:N)
    /\ !x:real^N^M. x$i$j = x$k1$k2` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[finite_index] THEN
     MESON_TAC[FINITE_INDEX_WORKS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[fnorm] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[GSYM REAL_ABS_POW] THEN
    REWRITE_TAC[real_abs; REAL_POW_2; REAL_LE_SQUARE] THEN
    SIMP_TAC [trace;transp;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    SUBGOAL_THEN
    `A$k1$k2 * (A:real^N^M)$k1$k2 =
        sum(1..dimindex(:N)) (\i.
        if (i = k2)
        then (sum (1..dimindex (:M)) (\k. if k = k1 then A$k1$k2 * A$k1$k2 else &0))
        else &0)` SUBST1_TAC THENL
    [SIMP_TAC [SUM_SUM_DELTA] THEN ASM_SIMP_TAC[IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN SIMP_TAC [FINITE_NUMSEG;IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
    [ALL_TAC; SIMP_TAC[sum_square]] THEN
    MATCH_MP_TAC SUM_LE THEN SIMP_TAC[FINITE_NUMSEG;IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [REAL_LE_REFL; REAL_LE_SQUARE]);;
  
let VECTOR_COMPONENT_LE_FNORM = prove
    (`!A:real^N^M i. norm(A$i) <= fnorm A`,
    REPEAT GEN_TAC THEN SUBGOAL_THEN
    `?k. 1 <= k /\ k <= dimindex(:M) /\ !x:real^N^M. x$i = x$k`
    STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[vector_norm;fnorm] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN 
    SIMP_TAC [SQRT_POW_2; DOT_POS_LE] THEN 
    SIMP_TAC [dot; matrix_mul; transp; trace; LAMBDA_BETA; CART_EQ] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
    `A$k$i' * (A:real^N^M)$k$i' =
        sum(1..dimindex(:M)) (\i. if i = k then A$k$i' * A$k$i' else &0)`
    SUBST1_TAC THENL
    [REWRITE_TAC[SUM_DELTA] THEN ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_REFL; REAL_LE_SQUARE]);;

let FNORM_LE_L1 = prove
    (`!A:real^N^M. fnorm A <= sum(1..dimindex(:N))(\i.sum(1..dimindex(:M)) (\k. abs(A$k$i)))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[fnorm] THEN 
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    SIMP_TAC[transp;trace;matrix_mul;CART_EQ;LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; REAL_LE_SQUARE; REAL_ABS_POS] THEN
    SPEC_TAC(`dimindex(:N)`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THENL
    [REAL_ARITH_TAC;ALL_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC(REAL_ARITH `a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)`) THEN
    ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS; FINITE_NUMSEG] THEN
    SPEC_TAC(`dimindex(:M)`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ARITH_RULE `1 <= SUC n`] THENL
    [REAL_ARITH_TAC;ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a2 <= a * a /\ &0 <= a * b /\ b2 <= b * b
    ==> a2 + b2 <= (a + b) * (a + b)`) THEN
    ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of the distance in matrix space             *)
(* ------------------------------------------------------------------------- *) 

override_interface("matrix_dist",`mdistance:real^N^M#real^N^M->real`);;

let matrix_dist = new_definition
    `matrix_dist(A,B) = fnorm(A - B)`;;

let MATRIX_DIST_REFL = prove
    (`!A:real^N^M. matrix_dist(A,A) = &0`,
    SIMP_TAC[matrix_dist;MATRIX_SUB_REFL;FNORM_0]);;

let MATRIX_DIST_POS_LE = prove
    (`!A:real^N^M B. &0 <= matrix_dist(A,B)`,
    REWRITE_TAC [matrix_dist;FNORM_POS_LE]);;
 
let MATRIX_DIST_EQ_0 = prove
    (`!A:real^N^M B. (matrix_dist(A,B) = &0) <=> (A = B)`,
    REPEAT GEN_TAC THEN METIS_TAC[matrix_dist;FNORM_EQ_0;MATRIX_SUB_EQ]);;
 
let MATRIX_DIST_SYM = prove
    (`!A:real^N^M B. matrix_dist(A,B) = matrix_dist(B,A)`,
    REPEAT GEN_TAC THEN METIS_TAC[matrix_dist;FNORM_SUB_SYM]);;

let REAL_ABS_MATRIX_DIST = prove
    (`!A B:real^N^M. abs(matrix_dist(A,B)) = matrix_dist(A,B)`,
    REPEAT GEN_TAC THEN METIS_TAC[matrix_dist;REAL_ABS_REFL;FNORM_POS_LE]);;
  
let MATRIX_DIST_TRIANGLE = prove
    (`!A:real^N^M B C. matrix_dist(A,C) <= matrix_dist(A,B) + matrix_dist(B,C)`,
    let MATRIX_SUB_TRANS = prove
    (`!A:real^N^M B C. A - C = (A - B) + (B - C)`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[matrix_add; CART_EQ; LAMBDA_BETA;matrix_sub] THEN
    ARITH_TAC) in
    REPEAT GEN_TAC THEN SIMP_TAC[matrix_dist] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MATRIX_SUB_TRANS] THEN
    SIMP_TAC[FNORM_TRIANGLE]);;
   
let MATRIX_DIST_TRIANGLE_ALT = prove
    (`!A:real^N^M B C. matrix_dist(B,C) <= matrix_dist(A,B) + matrix_dist(A,C)`,
    METIS_TAC[MATRIX_DIST_SYM;MATRIX_DIST_TRIANGLE]);;

let MATRIX_DIST_POS_LT = prove
    (`!A:real^N^M B. ~(A = B) ==> &0 < matrix_dist(A,B)`,
    METIS_TAC[matrix_dist;MATRIX_SUB_EQ;FNORM_POS_LT]);;
  
let MATRIX_DIST_NZ = prove
    (`!A:real^N^M B. ~(A = B) <=> &0 < matrix_dist(A,B)`,
    METIS_TAC[matrix_dist;MATRIX_SUB_EQ;FNORM_POS_LT]);;

let MATRIX_DIST_EQ = prove
    (`!A:real^N^M B C D. matrix_dist(A,B) = matrix_dist(C,D) <=> matrix_dist(A,B) pow 2 = matrix_dist(C,D) pow 2`,
    REWRITE_TAC[matrix_dist; FNORM_POW_2; FNORM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of  matrix space                            *)
(* ------------------------------------------------------------------------- *)

let matrix_open = new_definition
    `matrix_open s <=> !A:real^N^M. A IN s ==>
        ?e. &0 < e /\ !A'. matrix_dist(A',A) < e ==> A' IN s`;;
       
let matrix_space = new_definition
    `matrix_space = topology matrix_open`;;
 
let matrix_space_metric = new_definition
    `matrix_space_metric = metric ((:real^N^M), matrix_dist)`;;

let MATRIX_SPACE_METRIC = prove
    (`mdist (matrix_space_metric:(real^N^M)metric) = matrix_dist /\
    mspace matrix_space_metric = (:real^N^M)`,
    SUBGOAL_THEN `is_metric_space ((:real^N^M),matrix_dist)` MP_TAC THENL
    [REWRITE_TAC[is_metric_space; IN_UNIV; MATRIX_DIST_POS_LE; MATRIX_DIST_EQ_0;
                 MATRIX_DIST_SYM; MATRIX_DIST_TRIANGLE];
    SIMP_TAC[matrix_space_metric; MDIST; MSPACE]]);;
    
let OPEN_IN_MATRIX_SPACE_METRIC = prove
    (`open_in (mtopology matrix_space_metric) = matrix_open:(real^N^M->bool)->bool`,
    REWRITE_TAC[FUN_EQ_THM; OPEN_IN_MTOPOLOGY; matrix_open; MATRIX_SPACE_METRIC;
                SUBSET_UNIV; SUBSET; IN_MBALL; IN_UNIV; MATRIX_DIST_SYM]);;
             
let OPEN_IN_MATRIX_SPACE = prove
    (`open_in matrix_space = matrix_open`,
    REWRITE_TAC[matrix_space; GSYM OPEN_IN_MATRIX_SPACE_METRIC] THEN
    MESON_TAC[topology_tybij]);;
 
let MATRIX_OPEN_IN = prove
    (`!s:real^N^M->bool. matrix_open s <=> open_in matrix_space s`,
    REWRITE_TAC[OPEN_IN_MATRIX_SPACE]);;
    
let MTOPOLOGY_MATRIX_SPACE_METRIC = prove
    (`mtopology matrix_space_metric = matrix_space:(real^N^M)topology`,
    REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_MATRIX_SPACE_METRIC; MATRIX_OPEN_IN]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of the limit of matrix series               *)
(* ------------------------------------------------------------------------- *)
  
make_overloadable "->->" `:A->B->C->bool`;;

overload_interface ("->->",` matrixtendsto:(A->real^N^M)->real^N^M->(A)net->bool`);;

parse_as_infix("->->",(12,"right"));;

let matrixtendsto = new_definition
    `((f:A->real^N^M) ->-> l) net <=> !e. &0 < e ==> 
            eventually (\x. matrix_dist(f(x),l) < e) net`;;
  
let matrix_lim = new_definition  
    `! (f:A->real^N^M) net. matrix_lim net f = (@l. (f ->-> l) net)`;;

let LIMIT_MATRIX_SPACE = prove
    (`!f:A->real^N^M x net. limit matrix_space f x net <=> (f ->-> x) net`,
    REWRITE_TAC[LIMIT_METRIC; GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[MATRIX_SPACE_METRIC; IN_UNIV; matrixtendsto]);;
  
let MATRIX_LIM_UNIQUE = prove
    (`!net:(A)net f:A->real^N^M l:real^N^M l'.
      ~(trivial_limit net) /\ (f ->-> l) net /\ (f ->-> l') net ==> (l = l')`,
    REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC_UNIQUE]);;
  
let MATRIX_LIM_SEQUENTIALLY = prove
    (`!s l:real^N^M. (s ->-> l) sequentially <=>
            !e. &0 < e ==> ?N. !n. N <= n ==> matrix_dist(s(n),l) < e`,
    REWRITE_TAC[matrixtendsto; EVENTUALLY_SEQUENTIALLY] THEN MESON_TAC[]);;

let MATRIX_LIMIT_COMPONENTWISE_REAL = prove
    (`!net (f:A->real^N^M) l.
        limit matrix_space f l net <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> limit euclideanreal (\x. f x$i$j) (l$i$j) net`,
    let lem = prove
    (`!P. (!x y z. P x y z) <=> (!z x y. P x y z)`, METIS_TAC[]) in
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM MTOPOLOGY_MATRIX_SPACE_METRIC;
                GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC; MATRIX_SPACE_METRIC; REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[IN_UNIV; GSYM IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[MATRIX_DIST_SYM] THEN
    EQ_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
     MESON_TAC[MATRIX_SUB_COMPONENT; matrix_dist; 
               REAL_LET_TRANS; COMPONENT_LE_FNORM];
     REWRITE_TAC [GSYM RIGHT_FORALL_IMP_THM] THEN 
     X_GEN_TAC `e:real` THEN 
     ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN 
     STRIP_TAC THEN ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN 
     REWRITE_TAC [IMP_CONJ] THEN ONCE_REWRITE_TAC [lem] THEN
     REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN 
     SIMP_TAC[FORALL_EVENTUALLY; FINITE_NUMSEG; NUMSEG_EMPTY;
              NOT_LT; DIMINDEX_GE_1] THEN
     DISCH_THEN (MP_TAC o SPEC `e / (&(dimindex(:M)) * &(dimindex(:N)))`) THEN
     ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; 
                  REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN 
     X_GEN_TAC `x:A` THEN SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; matrix_dist] THEN 
     DISCH_TAC THEN W(MP_TAC o PART_MATCH lhand FNORM_LE_L1 o lhand o snd) THEN
     MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
     MATCH_MP_TAC SUM_SUM_BOUND_LT_GEN THEN
     ASM_SIMP_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1;
                  CARD_NUMSEG_1; GSYM IN_NUMSEG]]);;
                 
let MATRIX_LIMIT_COMPONENTWISE_VECTOR = prove
    (`!net (f:A->real^N^M) l.
        limit matrix_space f l net <=>
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> limit euclidean (\x. f x$i) (l$i) net`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM MTOPOLOGY_EUCLIDEAN_METRIC;
                GSYM MTOPOLOGY_MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC; EUCLIDEAN_METRIC; MATRIX_SPACE_METRIC] THEN
    REWRITE_TAC[IN_UNIV; RIGHT_IMP_FORALL_THM; GSYM IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC[FORALL_EVENTUALLY; FINITE_NUMSEG; NUMSEG_EMPTY;
             NOT_LT; DIMINDEX_GE_1] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC [] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
     X_GEN_TAC `x:A` THEN SIMP_TAC[matrix_dist; dist] THEN 
     SIMP_TAC [GSYM MATRIX_VECTOR_SUB_COMPONENT] THEN 
     METIS_TAC [VECTOR_COMPONENT_LE_FNORM; REAL_LET_TRANS];
     FIRST_X_ASSUM (MP_TAC o SPEC `e / (&(dimindex(:M)) * &(dimindex(:N)))`) THEN 
     ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; 
                  REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN 
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN BETA_TAC THEN
     REPEAT STRIP_TAC THEN SIMP_TAC [matrix_dist] THEN 
     W(MP_TAC o PART_MATCH lhand FNORM_LE_L1 o lhand o snd) THEN
     MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
     MATCH_MP_TAC SUM_SUM_BOUND_LT_GEN THEN
     ASM_SIMP_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1;
                  CARD_NUMSEG_1; GSYM IN_NUMSEG] THEN 
     REPEAT STRIP_TAC THEN 
     FIRST_X_ASSUM (MP_TAC o SPEC `k:num`) THEN 
     ASM_SIMP_TAC [dist; GSYM MATRIX_VECTOR_SUB_COMPONENT] THEN
     METIS_TAC [COMPONENT_LE_NORM; REAL_LET_TRANS]]);;
                         
let MATRIX_LIM_COMPONENTWISE_REAL = prove
    (`!net f:A->real^N^M l.
        (f ->-> l) net <=>
        !i j. (1 <= i /\ i <= dimindex(:M)) /\ (1 <= j /\ j <= dimindex(:N))
            ==> limit euclideanreal (\x. f x$i$j) (l$i$j) net`,
    REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; MATRIX_LIMIT_COMPONENTWISE_REAL]);;

let MATRIX_LIM_COMPONENTWISE_VECTOR = prove
    (`!net f:A->real^N^M l.
        (f ->-> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:M)
            ==> limit euclidean (\x. f x$i) (l$i) net`,
    REWRITE_TAC[GSYM LIMIT_MATRIX_SPACE; MATRIX_LIMIT_COMPONENTWISE_VECTOR]);;

let MATRIX_LIM_CONST = prove
    (`!net A:real^N^M. ((\x:A. A) ->-> A) net`,
    SIMP_TAC[matrixtendsto; MATRIX_DIST_REFL; EVENTUALLY_TRUE]);;
  
let MATRIX_LIM_CMUL = prove
    (`!net:(A)net f:A->real^N^M l c. (f ->-> l) net ==> ((\x. c %% f x) ->-> c %% l) net`,
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_CMUL_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_LMUL]);;
  
let MATRIX_LIM_NEG = prove
    (`!net:(A)net f:A->real^N^M l. (f ->-> l) net ==> ((\x. --(f x)) ->-> --l) net`,
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_NEG_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_NEG]);;
  
let MATRIX_LIM_ADD = prove
    (`!net:(A)net f:A->real^N^M g:A->real^N^M l m.
        (f ->-> l) net /\ (g ->-> m) net ==> ((\x. f(x) + g(x)) ->-> l + m) net`,
    REWRITE_TAC[MATRIX_LIM_COMPONENTWISE_REAL; MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC[LIMIT_REAL_ADD]);;
  
let MATRIX_LIM_SUB = prove
    (`!net:(A)net f:A->real^N^M g l m.
        (f ->-> l) net /\ (g ->-> m) net ==> ((\x. f(x) - g(x)) ->-> l - m) net`,
    REWRITE_TAC[real_sub; MATRIX_SUB] THEN ASM_SIMP_TAC[MATRIX_LIM_ADD; MATRIX_LIM_NEG]);;

(* ------------------------------------------------------------------------- *)
(* The definition and properties of the infinite sum of matrix serie         *)
(* ------------------------------------------------------------------------- *)  

parse_as_infix("msums",(12,"right"));;

let msums = new_definition
    `(f msums l) s = ((\n. msum(s INTER (0..n)) f) ->-> l) sequentially`;;

let infmsum = new_definition
    `infmsum s (f:num->real^N^M) = @l. (f msums l) s`;;

let msummable = new_definition
    `msummable s (f:num->real^N^M) = ?l. (f msums l) s`;;

let MSUMS_SUMMABLE = prove
    (`!f:num->real^N^M l s. (f msums l) s ==> msummable s f`,
    REWRITE_TAC[msummable] THEN METIS_TAC[]);;
  
let MSUMS_INFSUM = prove
    (`!f:num->real^N^M s. (f msums (infmsum s f)) s <=> msummable s f`,
    REWRITE_TAC[infmsum; msummable] THEN METIS_TAC[]);;
  
let MSUMS_LIM = prove
    (`!f:num->real^N^M s.
      (f msums matrix_lim sequentially (\n. msum (s INTER (0..n)) f)) s
      <=> msummable s f`,
    GEN_TAC THEN GEN_TAC THEN EQ_TAC THENL [MESON_TAC[msummable];
    REWRITE_TAC[msummable; msums] THEN STRIP_TAC THEN REWRITE_TAC[matrix_lim] THEN
    ASM_MESON_TAC[]]);;
    
let MSERIES_FROM = prove
    (`!f:num->real^N^M l k. 
        (f msums l) (from k) = ((\n. msum(k..n) f) ->-> l) sequentially`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; numseg; from; IN_ELIM_THM; IN_INTER] THEN ARITH_TAC);;
  
let MSERIES_UNIQUE = prove
    (`!f:num->real^N^M l l' s. (f msums l) s /\ (f msums l') s ==> (l = l')`,
    REWRITE_TAC[msums] THEN 
    MESON_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; MATRIX_LIM_UNIQUE]);;
  
let INFMSUM_UNIQUE = prove
    (`!f:num->real^N^M l s. (f msums l) s ==> infmsum s f = l`,
    MESON_TAC[MSERIES_UNIQUE; MSUMS_INFSUM; msummable]);;
                
let MSERIES_FINITE = prove
    (`!f:num->real^N^M s. FINITE s ==> (f msums (msum s f)) s`,
    REPEAT GEN_TAC THEN REWRITE_TAC[num_FINITE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[msums; MATRIX_LIM_SEQUENTIALLY] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `n:num` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s INTER (0..m) = s`
    (fun th -> ASM_REWRITE_TAC[th; MATRIX_DIST_REFL]) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG; LE_0] THEN
    ASM_MESON_TAC[LE_TRANS]);;
  
let MSERIES_ADD = prove
    (`!A:num->real^N^M A0 B B0 s.
     (A msums A0) s /\ (B msums B0) s ==> ((\n. A n + B n) msums (A0 + B0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_ADD; MATRIX_LIM_ADD]);;

let MSERIES_SUB = prove
    (`!A:num->real^N^M A0 B B0 s.
     (A msums A0) s /\ (B msums B0) s ==> ((\n. A n - B n) msums (A0 - B0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_SUB; MATRIX_LIM_SUB]);;

let MSERIES_CMUL = prove
    (`!A:num->real^N^M A0 c s. (A msums A0) s ==> ((\n. c %% A n) msums (c %% A0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_LMUL; MATRIX_LIM_CMUL]);;
  
let MSERIES_NEG = prove
    (`!A:num->real^N^M A0 s. (A msums A0) s ==> ((\n. --(A n)) msums (--A0)) s`,
    SIMP_TAC[msums; FINITE_INTER_NUMSEG; MSUM_NEG; MATRIX_LIM_NEG]);;
    
let MSERIES_TRIVIAL = prove
    (`!f:num->real^N^M. (f msums mat 0) {}`,
    REWRITE_TAC[msums; INTER_EMPTY; MSUM_CLAUSES; MATRIX_LIM_CONST]);;
   
let MSUMS_REINDEX = prove
    (`!k a l:real^N^M n.
   ((\x. a(x + k)) msums l) (from n) <=> (a msums l) (from(n + k))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[msums; FROM_INTER_NUMSEG] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MSUM_OFFSET] THEN
    REWRITE_TAC[MATRIX_LIM_SEQUENTIALLY] THEN
    ASM_MESON_TAC[ARITH_RULE `N + k:num <= n ==> n = (n - k) + k /\ N <= n - k`;
                ARITH_RULE `N + k:num <= n ==> N <= n + k`]);;
   
let MSERIES_EVEN = prove
    (`!f l:real^N^M n.
        (f msums l) (from n) <=>
        ((\i. if EVEN i then f(i DIV 2) else mat 0) msums l) (from (2 * n))`,
    let lemma = prove
    (`msum(2 * m..n) (\i. if EVEN i then f i else mat 0):real^N^M =
        msum(m..n DIV 2) (\i. f(2 * i))`,
    TRANS_TAC EQ_TRANS
     `msum (2 * m..2 * (n DIV 2) + 1)
           (\i. if EVEN i then f i else mat 0):real^N^M` THEN
    CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[MSUM_PAIR] THEN
     REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; MATRIX_ADD_RID]] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MSUM_EQ_SUPERSET THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET_NUMSEG] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `p = 2 * n DIV 2 + 1` SUBST1_TAC
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]) in
    REPEAT GEN_TAC THEN REWRITE_TAC[MSERIES_FROM; lemma] THEN
    REWRITE_TAC[ARITH_RULE `(2 * i) DIV 2 = i`; ETA_AX] THEN
    REWRITE_TAC[matrixtendsto] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ABBREV_TAC `P m <=> matrix_dist(msum (n..m) f:real^N^M,l) < e` THEN
    POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `2 * N` THEN ASM_SIMP_TAC[GSYM LE_RDIV_EQ; ARITH_EQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2 * n`) THEN
    REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;
  
let MSERIES_ODD = prove
    (`!f l:real^N^M n.
        (f msums l) (from n) <=>
        ((\i. if ODD i then f(i DIV 2) else mat 0) msums l) (from (2 * n + 1))`,
    REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MSERIES_EVEN] THEN
    REWRITE_TAC[GSYM MSUMS_REINDEX] THEN
    REWRITE_TAC[ODD_ADD; ARITH_ODD; NOT_ODD] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[ARITH_RULE `(2 * m + 1) DIV 2 = m`] THEN
    REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m`]);;

(* ------------------------------------------------------------------------- *)
(* Rodrigues's formula when |w|=1                                            *)
(* ------------------------------------------------------------------------- *)  

let matrix_exp = new_definition
    `!A:real^N^N. matrix_exp A = 
                infmsum (from 0) (\n. (&1 / &(FACT n)) %% (A matrix_pow n))`;;

let MSUM_CASES_3 = prove
    (`!s:A->bool P Q f g k. FINITE s
    ==> msum s (\x:A. if P x then (f x):real^N^M 
                      else if Q x then (g x):real^N^M else (k x):real^N^M) =
        msum {x | x IN s /\ P x} f + msum {x | x IN s /\ ~P x /\ Q x} g +
        msum {x | x IN s /\ ~P x /\ ~Q x} k`,
    let lem = prove
    (`!D:real^N^M. A + B = A + C + D <=> B = C + D`,
    ONCE_REWRITE_TAC[GSYM MATRIX_SUB_EQ] THEN
    SIMP_TAC[matrix_sub;matrix_add;CART_EQ;LAMBDA_BETA;MAT_0_COMPONENT] THEN
    SIMP_TAC[REAL_ARITH `(a + b) - (a + c + d) = b - (c + d)`]) in
    SIMP_TAC[MSUM_CASES] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC[lem] THEN
    SUBGOAL_THEN `FINITE ((s:A->bool) DIFF P)` MP_TAC THENL
    [MATCH_MP_TAC FINITE_DIFF THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[DIFF;IN;MSUM_CASES] THEN 
    SIMP_TAC[IN_ELIM_THM;TAUT `(s x /\ ~P x) /\ Q x <=> s x /\ ~P x /\ Q x`]);;

let COND_DOUBLE_RAND = prove
    (`!b c (f:A->B) x y z. f (if b then x else if c then y else z) = (if b then f x else if c then f y else f z)`,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN 
    SIMP_TAC[COND_RAND;COND_ID]);;
  
let RODRIGUES_FORMULA = prove
    (`! w:real^3 a:real. (norm w = &1) ==> matrix_exp (a %% vec3_2_ssm w) =
                    (mat 1:real^3^3) + sin(a) %% vec3_2_ssm w + 
                    (&1 - cos(a)) %% (vec3_2_ssm w) matrix_pow 2`,
    let lem1 = SPECL [`(-- &1 pow (x DIV 2 - 1))`] REAL_MUL_LID in
    let lem2 = SPECL [`(&1)`;`(-- &1 pow (x DIV 2 - 1))`] REAL_NEG_LMUL in
    let even_lem1 = prove
        (`EVEN INTER {x' | x' <= x} = EVEN INTER {x' | 0 <= x' /\ x' <= x}`,
        SIMP_TAC[INTER;IN;IN_ELIM_THM] THEN REWRITE_TAC[EXTENSION] THEN
        SIMP_TAC[IN_ELIM_THM] THEN MESON_TAC[LE_0]) in
    let even_lem2 = prove
        (`(EVEN INTER (0..n)) DELETE 0 = EVEN INTER (1..n)`,
        SIMP_TAC[SET_RULE `(EVEN INTER (0..n)) DELETE 0 = EVEN INTER ((0..n) DELETE 0)`] THEN SIMP_TAC[DELETE;numseg;IN_ELIM_THM] THEN
        SIMP_TAC [ARITH_RULE `(1 <= y) <=> 0 <= y /\ ~(y = 0)`] THEN
        SET_TAC[]) in    
    let even_lem3 = prove
        (`(EVEN INTER (1..n))= EVEN INTER (2..n)`,
        let lem1 = SPECL [`1`;`x:num`] LE_LT in
        SIMP_TAC[numseg;INTER;IN;IN_ELIM_THM] THEN
        SIMP_TAC [lem1] THEN
        SIMP_TAC[SET_RULE `EVEN x /\ (1 < x \/ 1 = x) /\ x <= n <=> ((EVEN x /\ 1 < x) \/ (EVEN x /\ 1 = x)) /\ x <= n`] THEN
        SIMP_TAC[ARITH_RULE `1 < x <=> 2 <= x`] THEN
        SIMP_TAC[SET_RULE `(EVEN x /\ 1 = x) <=> x IN EVEN INTER {1}`] THEN
        SIMP_TAC[SET_RULE `~(EVEN 1) ==> (EVEN INTER {1}) = EMPTY`;ARITH_RULE `~(EVEN 1)`] THEN SET_TAC[]) in
    let odd_lem1 = prove
        (`!x. ODD x ==> (x DIV 2 = (x -1) DIV 2)`,
        let lem = ARITH_RULE `~ (2 = 0)` in
        let lem2 = SPECL [`n:num`;`2`] DIVISION in
        let lem3 = CONJUNCT1 (MATCH_MP lem2 lem) in
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC (ARITH_RULE `x * 2 = y * 2 ==> x = y`) THEN
        MATCH_MP_TAC (ARITH_RULE `!x y z:num. x + z = y + z ==> x = y`) THEN
        EXISTS_TAC `x MOD 2` THEN REWRITE_TAC [GSYM lem3] THEN
        ASM_SIMP_TAC [MESON [ODD_MOD] `ODD x ==> x MOD 2 = 1`] THEN
        SUBGOAL_THEN `EVEN (x - 1)` ASSUME_TAC THENL
        [REWRITE_TAC [GSYM NOT_ODD;ODD_SUB;DE_MORGAN_THM] THEN
         SIMP_TAC [ARITH_RULE `~(1 < x) = (x = 0 \/ x = 1)`] THEN
         ASM_MESON_TAC [ODD; num_CONV `1`]; ALL_TAC] THEN
        ASM_SIMP_TAC[EVEN_DIV2] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
        MATCH_MP_TAC SUB_ADD THEN SIMP_TAC [ARITH_RULE `1 <= x <=>  ~(x = 0) `] THEN
        ASM_MESON_TAC [ODD]) in
    let odd_lem2 = prove
        (`!x. ODD x ==> (2 * x DIV 2 + 1 = x)`,
        let lem = ARITH_RULE `~ (2 = 0)` in
        let lem2 = SPECL [`n:num`;`2`] DIVISION in
        let lem3 = CONJUNCT1 (MATCH_MP lem2 lem) in
        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC [MESON [ODD_MOD] `ODD x ==> 1 = x MOD 2`] THEN
        MESON_TAC[MULT_SYM; GSYM lem3]) in
    let odd_lem3 = prove
        (`{n' | n' IN 0..n /\ ~(n' = 0) /\ ~EVEN n'} = ODD INTER (1..n)`,
        SIMP_TAC[NOT_EVEN;IN;INTER;numseg;IN_ELIM_THM] THEN
        SIMP_TAC [ARITH_RULE `(1 <= y) <=> 0 <= y /\ ~(y = 0)`] THEN
        SET_TAC[]) in
    SIMP_TAC[matrix_exp;MATRIX_POW_CMUL;MATRIX_POW_2;MATRIX_CMUL_ASSOC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INFMSUM_UNIQUE THEN
    ASM_SIMP_TAC[SSM_POW_N] THEN SIMP_TAC[COND_DOUBLE_RAND;MSERIES_FROM] THEN
    SIMP_TAC[FACT;real_pow;REAL_ARITH `(&1 / &1 * &1) = &1`] THEN 
    SIMP_TAC[GSYM MAT_CMUL;MATRIX_CMUL_ASSOC] THEN
    SIMP_TAC[FINITE_NUMSEG;MSUM_CASES_3] THEN
    (*prove 1. n = 0*)
    MATCH_MP_TAC MATRIX_LIM_ADD THEN CONJ_TAC THENL
    [SIMP_TAC[IN_NUMSEG] THEN
     SIMP_TAC[ARITH_RULE `(0 <= n' /\ n' <= n) /\ n' = 0 <=> (n' = 0)`] THEN
     SIMP_TAC[SET_RULE `{n' | n' = 0} = {0}`;MSUM_SING] THEN
     SIMP_TAC[matrixtendsto;MATRIX_DIST_REFL;EVENTUALLY_SEQUENTIALLY];
     ALL_TAC] THEN
     (*prove 2. EVEN n (&1 - cos (a))*)
    ONCE_SIMP_TAC[MATRIX_ADD_SYM] THEN
    MATCH_MP_TAC MATRIX_LIM_ADD THEN CONJ_TAC THENL
    [SIMP_TAC[MSUM_RMUL] THEN
     SIMP_TAC[SET_RULE `{n' | n' IN 0..n /\ ~(n' = 0) /\ EVEN n'} = {n' | n' IN 0..n /\ EVEN n'} DELETE 0`] THEN
     SIMP_TAC[SET_RULE `{n' | n' IN 0..n /\ EVEN n'} = (EVEN INTER (0..n))`] THEN
     (* matrix ==> real *)
     SIMP_TAC[MATRIX_LIM_COMPONENTWISE_REAL] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
     ASM_SIMP_TAC [MATRIX_CMUL_COMPONENT] THEN MATCH_MP_TAC LIMIT_REAL_RMUL THEN
     (*prove in real_space*)
     ONCE_REWRITE_TAC[REAL_ARITH  `sum s f = -- --(sum s f)`] THEN
     ONCE_REWRITE_TAC[GSYM SUM_NEG] THEN SIMP_TAC[ETA_AX] THEN
     SIMP_TAC[GSYM REAL_MUL_RNEG;REAL_ARITH `(&1 - cos a) = --(cos a - &1)`] THEN
     ONCE_REWRITE_TAC[GSYM lem1] THEN ONCE_REWRITE_TAC[lem2] THEN
     SIMP_TAC[ARITH_RULE `-- &1 * -- &1 pow (x DIV 2 - 1) = (-- &1 pow (x DIV 2 - 1)) * ((-- &1) pow 1)`] THEN
     SIMP_TAC[GSYM REAL_POW_ADD;even_lem2;even_lem3] THEN 
     SIMP_TAC[ARITH_RULE `2 <= x ==> (x DIV 2 - 1 + 1) = (x DIV 2)`;numseg;INTER;IN_ELIM_THM;IN;ARITH] THEN
     ONCE_SIMP_TAC[SET_RULE `2 <= x /\ x <= n <=> {x | 2 <= x /\ x <= n} x`] THEN
     SIMP_TAC[GSYM numseg;SET_RULE `{x | EVEN x /\ (2..n) x} = EVEN INTER (2..n)`] THEN
     SIMP_TAC[GSYM even_lem3;GSYM even_lem2] THEN
     MATCH_MP_TAC LIMIT_REAL_NEG THEN SIMP_TAC[LIMIT_EUCLIDEANREAL] THEN
     (* prove the first item of cos(a)*)
     SIMP_TAC[SUM_DELETE;FINITE_NUMSEG;FINITE_INTER;IN_INTER;numseg;ARITH;IN_ELIM_THM;IN;EVEN;LE_0] THEN
     SIMP_TAC[FACT;real_pow;ARITH_RULE `(0 DIV 2) = 0`;
              REAL_ARITH `(&1 / &1 * &1) * &1 = &1`] THEN
     SIMP_TAC[even_lem1; GSYM numseg] THEN
     MATCH_MP_TAC REALLIM_SUB THEN SIMP_TAC[REALLIM_CONST] THEN
     (* prove cos(a)*)
     MP_TAC COS_CONVERGES THEN
     ONCE_REWRITE_TAC [REAL_SERIES_EVEN] THEN
     SIMP_TAC[MULT_SYM;EVEN_DIV2;ARITH_RULE `2 * 0 = 0`] THEN
     SIMP_TAC[from;LE_0;SET_RULE `EVEN i <=> i IN EVEN`;
              UNIV_GSPEC;REAL_SERIES_RESTRICT] THEN
     SIMP_TAC[ARITH_RULE `((&1 / &(FACT i) * a pow i) * -- &1 pow (i DIV 2)) = (-- &1 pow (i DIV 2) * a pow i / &(FACT i))`] THEN
     SIMP_TAC[real_sums] ; ALL_TAC] THEN
    (*prove 3. ODD n (sin(a))*)
    SIMP_TAC[MSUM_RMUL;odd_lem3] THEN
    SIMP_TAC[MATRIX_LIM_COMPONENTWISE_REAL] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC [MATRIX_CMUL_COMPONENT] THEN
    MATCH_MP_TAC LIMIT_REAL_RMUL THEN
    SIMP_TAC[LIMIT_EUCLIDEANREAL] THEN
    MP_TAC SIN_CONVERGES THEN
    ONCE_REWRITE_TAC [REAL_SERIES_ODD] THEN
    SIMP_TAC[ARITH_RULE `2 * 0 + 1 = 1`] THEN
    SIMP_TAC[odd_lem1;odd_lem2;REAL_SERIES_FROM;GSYM SUM_RESTRICT_SET] THEN
    SIMP_TAC[SET_RULE `{i | i IN 1..n /\ ODD i} = ODD INTER (1..n)`] THEN
    SIMP_TAC[ARITH_RULE `((&1 / &(FACT i) * a pow i) * -- &1 pow ((i - 1) DIV 2)) = (-- &1 pow ((i - 1) DIV 2) * a pow i / &(FACT i))`]);;

let RODRIGUES_FORMULA_COMPONENT = prove
    (`! w:real^3 a:real. (norm w = &1) ==> 
        matrix_exp (a %% vec3_2_ssm w) =
        vector[vector[((w$1 pow 2) * (&1 - cos(a)) + cos(a));
                      (w$1 * w$2 * (&1 - cos(a)) - w$3 * sin(a));
                      (w$1 * w$3 * (&1 - cos(a)) + w$2 * sin(a))];
               vector[(w$1 * w$2 * (&1 - cos(a)) + w$3 * sin(a));
                      ((w$2 pow 2) * (&1 - cos(a)) + cos(a));
                      (w$2 * w$3 * (&1 - cos(a)) - w$1 * sin(a))];
               vector[(w$1 * w$3 * (&1 - cos(a)) - w$2 * sin(a));
                      (w$2 * w$3 * (&1 - cos(a)) + w$1 * sin(a));
                      ((w$3 pow 2) * (&1 - cos(a)) + cos(a))]]:real^3^3`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[SSM_POW_2;RODRIGUES_FORMULA] THEN                  
    SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;mat;vec3_2_ssm;vec3_vtrans;matrix_cmul;matrix_sub;matrix_add] THEN
    SIMP_TAC[REAL_POW_2;ARITH] THEN
    SIMP_TAC[real_sub;REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_RZERO;REAL_MUL_LZERO;REAL_ADD_AC;REAL_ADD_LID;REAL_ADD_RID;REAL_ADD_RINV;REAL_ADD_LINV;REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_NEG_NEG;REAL_NEG_ADD;REAL_MUL_AC;REAL_NEG_0;VECTOR_NEG_COMPONENT]);;
    
let RODRIGUES_FORMULA_ALT = prove
    (`! w:real^3 a:real. (norm w = &1) ==> matrix_exp (a %% vec3_2_ssm w) =
                    cos(a) %% (mat 1:real^3^3) + sin(a) %% vec3_2_ssm w + 
                    (&1 - cos(a)) %% (vec3_vtrans w)`,
    SIMP_TAC[RODRIGUES_FORMULA;SSM_POW_2;MATRIX_CMUL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATRIX_CMUL_SUB_RDISTRIB] THEN REWRITE_TAC[MATRIX_CMUL_LID;MATRIX_SUB;MATRIX_NEG_SUB] THEN
    ONCE_REWRITE_TAC[MATRIX_ADD_SYM] THEN
    REWRITE_TAC[GSYM MATRIX_ADD_ASSOC;MATRIX_ADD_LNEG;MATRIX_ADD_RID]);;

(*
let ORTHOGONAL_MATRIX_EQ = prove
    (`!A:real^N^N. orthogonal_matrix A <=> matrix_inv A = transp A /\ invertible A`,
    GEN_TAC THEN EQ_TAC THENL
    [SIMP_TAC[ORTHOGONAL_MATRIX_INV;ORTHOGONAL_MATRIX_IMP_INVERTIBLE];
     REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal_matrix] THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[MATRIX_INV]]);;
     
let INVERTIBLE_MATRIX_EXP = prove    
    (`!x t. invertible (matrix_exp (t %% x))`,
    REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    MESON_TAC[MATRIX_EXP_INV_FUN;LIFT_DROP2]);;

let ORTHOGONAL_RODRIGUES = prove
    (`!w:real^3 a:real. (norm w = &1) ==> 
    orthogonal_matrix (matrix_exp (a %% vec3_2_ssm w))`,
    REWRITE_TAC[ORTHOGONAL_MATRIX_EQ;INVERTIBLE_MATRIX_EXP;TRANSP_TRANS_EXP;MATRIX_EXP_INV;MATRIX_ARITH `!x t. --(t %% x) = t %% (--x)`;VEC3_SSM_TRANSP]);;

let ROTATION_RODRIGUES = prove    
    (`! w:real^3 a:real. (norm w = &1) ==> 
        rotation_matrix (matrix_exp (a %% vec3_2_ssm w))`,
    let lem = MESON [ETA_AX]`det (matrix_exp (a %% vec3_2_ssm w))= (\x. det (matrix_exp (x %% vec3_2_ssm w))) a` in
    SIMP_TAC[rotation_matrix;ORTHOGONAL_RODRIGUES] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[lem] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONST_UNIQUE THEN
    EXISTS_TAC `-- &1` THEN
    ASM_SIMP_TAC[DET_ORTHOGONAL_MATRIX;ORTHOGONAL_RODRIGUES;DET_EXP_REAL_CONTINUOUS_AT] THEN 
    EXISTS_TAC `&0` THEN
    REWRITE_TAC[MATRIX_CMUL_LZERO;MATRIX_EXP_0;DET_I]);;
*)

(* ------------------------------------------------------------------------- *)
(* Rodrigues parameter and the Cayley decomposition form of Rodrigues matrix *)
(* ------------------------------------------------------------------------- *)
    
let rodrigues_parameter = new_definition
    `rodrigues_parameter (a:real) (w:real^3) = tan(a * inv(&2)) % w`;;
    
let INVERTIBLE_MAT_ADD_SSM = prove
    (`!w:real^3 a:real. invertible(mat 1 + vec3_2_ssm(rodrigues_parameter a w))`,
    let lem = prove
    (`!a:real^3. mat 1 + vec3_2_ssm a = 
        vector[vector [&1; --a$3; a$2]; vector [a$3; &1; --a$1];
               vector [--a$2; a$1; &1]]:real^3^3`,
    SIMP_TAC[CART_EQ;LAMBDA_BETA;DIMINDEX_3;FORALL_3;VECTOR_3;MAT_COMPONENT;MATRIX_ADD_COMPONENT;vec3_2_ssm;ARITH] THEN ARITH_TAC) in
    REWRITE_TAC[INVERTIBLE_DET_NZ;DET_3;VECTOR_3;lem;VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_NEG_NEG;REAL_MUL_LID;REAL_MUL_RID;REAL_SUB_RNEG] THEN
    SIMP_TAC[REAL_LE_SQUARE;REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 < (&1 + --(z * x * y) + ((y * z * x + a) + c) + b)`;REAL_ARITH `&0 < x ==> ~(x = &0)`]);;
    
let INVERTIBLE_MAT_SUB_SSM = prove
    (`!w:real^3 a:real. invertible(mat 1 - vec3_2_ssm(rodrigues_parameter a w))`,
    ONCE_REWRITE_TAC[GSYM INVERTIBLE_TRANSP] THEN
    REWRITE_TAC[VEC3_SSM_TRANSP_SUB;INVERTIBLE_MAT_ADD_SSM]);;

let RODRIGUES_FORMULA_CAYLEY_ALT = prove
    (`!w:real^3 a:real. (norm w = &1)  /\ ~(cos (a * inv (&2)) = &0) ==>
    matrix_exp (a %% vec3_2_ssm w) = transp (inv (&1 + ((rodrigues_parameter a w) dot (rodrigues_parameter a w))) %% ((&1 - ((rodrigues_parameter a w) dot (rodrigues_parameter a w))) %% mat 1 + &2 %% vec3_vtrans(rodrigues_parameter a w) - &2 %% vec3_2_ssm(rodrigues_parameter a w)))`,
    let lem1 = REWRITE_RULE [REAL_ARITH `(a * inv (&2)) * &2 = a`] (ISPEC ` a * inv(&2)` COS_DOUBLE_TAN) in
    let lem2 = REWRITE_RULE [REAL_ARITH `(a * inv (&2)) * &2 = a`] (ISPEC ` a * inv(&2)` COS_DOUBLE_TAN_ALT) in
    let lem3 = REWRITE_RULE [REAL_ARITH `(a * inv (&2)) * &2 = a`] (ISPEC `a * inv(&2)` SIN_DOUBLE_TAN) in
    SIMP_TAC[RODRIGUES_FORMULA_COMPONENT;rodrigues_parameter;DOT_LMUL;DOT_RMUL;VEC3_VTRANS_CMUL;VEC3_SSM_CMUL;MATRIX_CMUL_ASSOC;REAL_POW_2;VEC3_NORM_EQ_1] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;mat;vec3_vtrans;vec3_2_ssm;VECTOR_NEG_COMPONENT;matrix_cmul;matrix_sub;matrix_add;DOT_3;transp;ARITH] THEN
    SIMP_TAC[REAL_MUL_RID;REAL_MUL_RZERO;REAL_ADD_LID;REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC[lem1;lem2;lem3] THEN
    REAL_ARITH_TAC);;
  
let RODRIGUES_FORMULA_CAYLEY_ALT_COMPONENT = prove
    (`!w:real^3 a:real. (norm w = &1)  /\ ~(cos (a * inv (&2)) = &0) ==>
    matrix_exp (a %% vec3_2_ssm w) = 
    transp(inv (&1 + ((rodrigues_parameter a w) dot (rodrigues_parameter a w))) %% vector[vector[&1 + (rodrigues_parameter a w)$1 pow 2 - (rodrigues_parameter a w)$2 pow 2 -(rodrigues_parameter a w)$3 pow 2;
                  &2 * ((rodrigues_parameter a w)$1 * (rodrigues_parameter a w)$2 + (rodrigues_parameter a w)$3);
                  &2 * ((rodrigues_parameter a w)$1 * (rodrigues_parameter a w)$3 - (rodrigues_parameter a w)$2)];
           vector[&2 * ((rodrigues_parameter a w)$1 * (rodrigues_parameter a w)$2 - (rodrigues_parameter a w)$3);
                  &1 - (rodrigues_parameter a w)$1 pow 2 + (rodrigues_parameter a w)$2 pow 2 -(rodrigues_parameter a w)$3 pow 2;
                  &2 * ((rodrigues_parameter a w)$2 * (rodrigues_parameter a w)$3 + (rodrigues_parameter a w)$1)];
           vector[&2 * ((rodrigues_parameter a w)$1 * (rodrigues_parameter a w)$3 + (rodrigues_parameter a w)$2);
                  &2 * ((rodrigues_parameter a w)$2 * (rodrigues_parameter a w)$3 - (rodrigues_parameter a w)$1);
                  &1 - (rodrigues_parameter a w)$1 pow 2 - (rodrigues_parameter a w)$2 pow 2 + (rodrigues_parameter a w)$3 pow 2]]:real^3^3)`,
    let lem = prove
    (`!x y z c.  x * x + y * y + z * z = &1 ==> (&2 * c * c) * x * x = (c * c) * &1 + (c * c) * x * x - (c * c) * y * y - (c * c) * z * z`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ARITH_TAC) in              
    let lem1 = REAL_ARITH `!x y z. x * x + y * y + z * z = &1 ==> (y * y + x * x + z * z = &1 /\ z * z + y * y + x * x = &1)` in
    SIMP_TAC[RODRIGUES_FORMULA_CAYLEY_ALT] THEN
    SIMP_TAC[rodrigues_parameter;DOT_LMUL;DOT_RMUL;VEC3_VTRANS_CMUL;VEC3_SSM_CMUL;MATRIX_CMUL_ASSOC;REAL_POW_2;VEC3_NORM_EQ_1] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;mat;vec3_vtrans;vec3_2_ssm;VECTOR_NEG_COMPONENT;matrix_cmul;matrix_sub;matrix_add;DOT_3;transp;VECTOR_MUL_COMPONENT;ARITH] THEN
    REWRITE_TAC[REAL_ARITH `!c x y. (c * x) * (c * y) = (c * c) * x * y`] THEN
    SIMP_TAC[REAL_MUL_RID;REAL_MUL_RZERO;REAL_ADD_LID;REAL_SUB_RZERO] THEN
    MP_TAC (ISPECL [`(w:real^3)$1`;`(w:real^3)$2`;`(w:real^3)$3`;`tan (a * inv (&2))`] lem) THEN
    MP_TAC (ISPECL [`(w:real^3)$2`;`(w:real^3)$1`;`(w:real^3)$3`;`tan (a * inv (&2))`] lem) THEN
    MP_TAC (ISPECL [`(w:real^3)$3`;`(w:real^3)$2`;`(w:real^3)$1`;`tan (a * inv (&2))`] lem) THEN
    ASM_SIMP_TAC[lem1] THEN ARITH_TAC);;
    
let RODRIGUES_FORMULA_CAYLEY = prove    
    (`!w:real^3 a:real. (norm w = &1)  /\ ~(cos (a * inv (&2)) = &0) ==>
    matrix_exp (a %% vec3_2_ssm w) = transp((mat 1 - vec3_2_ssm(rodrigues_parameter a w)) ** matrix_inv(mat 1 + vec3_2_ssm(rodrigues_parameter a w)))`,
    let lem1 = MESON [REAL_LE_SQUARE;REAL_ARITH `!c. &0 <= c * c ==> ~(&1 + c * c = &0)`] `!c. ~(&1 + c * c = &0)` in
    let lem2 = prove
    (`!x y c. ~(x = &0) ==> (inv(x) * y = c <=> y = c * x)`,
    REPEAT STRIP_TAC THEN 
    ONCE_REWRITE_TAC[REAL_ARITH `inv(x) * y = c <=> y * inv(x) = c * &1`] THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_RINV;REAL_MUL_ASSOC;REAL_EQ_MUL_RCANCEL;REAL_INV_EQ_0]) in
    let lem3 = MESON [REAL_MUL_RID] `!x y z c. x * x + y * y + z * z = &1 ==> &1 + c * c = &1 + (c * c) * (x * x + y * y + z * z)` in
    REWRITE_TAC[MATRIX_TRANSP_MUL;TRANSP_MATRIX_INV] THEN
    SIMP_TAC[GSYM (ISPECL [`transp(mat 1 + vec3_2_ssm (rodrigues_parameter a w))`;`matrix_exp (a %% vec3_2_ssm w)`;`matrix_inv (transp (mat 1 + vec3_2_ssm (rodrigues_parameter a w))) ** transp (mat 1 - vec3_2_ssm (rodrigues_parameter a w))`] MATRIX_MUL_LCANCEL); INVERTIBLE_TRANSP;INVERTIBLE_MAT_ADD_SSM] THEN
    SIMP_TAC[MATRIX_MUL_ASSOC;INVERTIBLE_MAT_SUB_SSM;MATRIX_INV;MATRIX_MUL_LID;VEC3_SSM_TRANSP_ADD;VEC3_SSM_TRANSP_SUB] THEN
    SIMP_TAC[RODRIGUES_FORMULA_CAYLEY_ALT_COMPONENT] THEN
    SIMP_TAC[rodrigues_parameter;DOT_LMUL;DOT_RMUL;VEC3_VTRANS_CMUL;VEC3_SSM_CMUL;MATRIX_CMUL_ASSOC;REAL_POW_2;VEC3_NORM_EQ_1] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `tan (a * inv (&2))` lem1) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;mat;vec3_vtrans;vec3_2_ssm;VECTOR_NEG_COMPONENT;matrix_cmul;matrix_sub;matrix_add;DOT_3;transp;VECTOR_MUL_COMPONENT;matrix_mul;SUM_3;ARITH] THEN
    REWRITE_TAC[REAL_ARITH `!c x y. (c * x) * (c * y) = (c * c) * x * y`] THEN
    SIMP_TAC[REAL_MUL_RID;REAL_MUL_LID;REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_LZERO;REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_ARITH `x * inv (&1 + c * c) * y = inv (&1 + c * c) * y * x`] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[lem2] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    MP_TAC(ISPECL [`(w:real^3)$1`;`(w:real^3)$2`;`(w:real^3)$3`;`tan (a * inv (&2))`] lem3) THEN ANTS_TAC THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
    SIMP_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The relationship of the movement of vectors                               *)
(* ------------------------------------------------------------------------- *)
    
let normalized_vector = new_definition
    `normalized_vector (v:real^N) = inv(norm(v)) % v`;;

let rot_matrix = new_definition
    `rot_matrix (a:real) (w:real^3) = matrix_exp (a %% vec3_2_ssm w)`;;
    
let rotate_vector = new_definition
    `rotate_vector (a:real) (w:real^3) (v:real^3) = matrix_exp (a %% vec3_2_ssm w) ** v`;;
    
let translate_vector = new_definition
    `translate_vector (a:real) (w:real^3) (v:real^3) = -- (matrix_exp (a %% vec3_2_ssm w) ** v)`;;
    
let ROTATION_RELATION_RODRIGUES_CAYLAY = prove
    (`!w:real^3 v a:real. (norm w = &1)  /\ ~(cos (a * inv (&2)) = &0) ==> 
    rotate_vector a w v =  transp((mat 1 - vec3_2_ssm(rodrigues_parameter a w)) ** matrix_inv(mat 1 + vec3_2_ssm(rodrigues_parameter a w))) ** v`,
    SIMP_TAC[rotate_vector;RODRIGUES_FORMULA_CAYLEY]);;
    
let ROTATION_RELATION_RODRIGUES_CAYLAY_EQ = prove
    (`!w:real^3 v a:real. (norm w = &1)  /\ ~(cos (a * inv (&2)) = &0) ==> 
    transp(mat 1 + vec3_2_ssm(rodrigues_parameter a w)) ** rotate_vector a w v =  transp(mat 1 - vec3_2_ssm(rodrigues_parameter a w)) ** v`,
    SIMP_TAC[ROTATION_RELATION_RODRIGUES_CAYLAY;MATRIX_TRANSP_MUL;GSYM MATRIX_INV_TRANSP] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC;MATRIX_INV;MATRIX_MUL_LID;VEC3_SSM_TRANSP_ADD;INVERTIBLE_MAT_SUB_SSM]);;
    
let ROTATION_RELATION_RODRIGUES_PARAMETER = prove
    (`!w:real^3 v a:real. (norm w = &1)  /\ ~(cos (a * inv (&2)) = &0) ==> 
    vec3_2_ssm(v + (rotate_vector a w v)) ** (rodrigues_parameter a w) = v - (rotate_vector a w v)`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPECL [`w:real^3`;`v:real^3`;`a:real`] ROTATION_RELATION_RODRIGUES_CAYLAY_EQ) THEN
    ASM_SIMP_TAC[VEC3_SSM_TRANSP_ADD;VEC3_SSM_TRANSP_SUB] THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SIMP_TAC[vec3_2_ssm;CART_EQ;LAMBDA_BETA;FORALL_3;DIMINDEX_3;VECTOR_3;SUM_3;VECTOR_ADD_COMPONENT;VECTOR_SUB_COMPONENT;MATRIX_VECTOR_MUL_COMPONENT;dot;mat;matrix_sub;matrix_add;VECTOR_NEG_COMPONENT] THEN
    ARITH_TAC);;
    
(* ------------------------------------------------------------------------- *)
(* Least square                                                              *)
(* ------------------------------------------------------------------------- *)

let MIN_LEAST_SQUARE = 
(`!A:real^N^M x y:real^M.  transp A ** (A ** x - y) = vec 0 ==> (!k. norm(A ** x - y) <= norm(A ** k - y))`,
REPEAT GEN_TAC THEN
GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [(ISPEC `((A:real^N^M) ** (x:real^N))` (VECTOR_ARITH `!x y k:real^M. k - y = (x - y) + (k - x)`))] THEN
SIMP_TAC[VECTOR_SUB_REFL;VECTOR_ADD_RID] THEN
SIMP_TAC[GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB;NORM_LE] THEN
SIMP_TAC[DOT_LADD;DOT_RADD] THEN 
SIMP_TAC[REAL_ARITH `a <= (a + b) + c + d <=> &0 <= b + c + d`] THEN
SIMP_TAC[MESON [REAL_MUL_2;REAL_ADD_AC;DOT_SYM] `a dot b + b dot a + c = &2 * (a dot b) + c`] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC REAL_LE_ADD THEN SIMP_TAC[DOT_POS_LE] THEN 
ASM_SIMP_TAC[GSYM DOT_MATRIX_TRANSP_LMUL;DOT_LZERO;REAL_MUL_RZERO;REAL_LE_REFL]);;

let LEAST_SQUARE_HAS_SOLUTION = prove
    (`!A:real^N^M y:real^M. (?x. A ** x = y) <=> (A ** matrix_inv A ** y = y)`,
    REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
     SIMP_TAC[GSYM MATRIX_MUL_ASSOC;MATRIX_INV_MUL_INNER];ALL_TAC] THEN
    EXISTS_TAC `matrix_inv (A:real^N^M) ** y` THEN ASM_SIMP_TAC[]);;
  
let LEAST_SQUARE_GENERAL_SOLUTION = prove
    (`!A:real^N^M y. (?x. A ** x = y) ==> (!x. A ** x = y <=> (?z. x = matrix_inv A ** y + (mat 1 - matrix_inv A ** A) ** z))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [LEAST_SQUARE_HAS_SOLUTION]) THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [EXISTS_TAC `x:real^N` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC;ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB;MATRIX_VECTOR_MUL_ASSOC;MATRIX_SUB_LDISTRIB;MATRIX_MUL_RID;MATRIX_INV_MUL_INNER] THEN
    SIMP_TAC[MATRIX_SUB_REFL;MATRIX_VECTOR_MUL_LZERO;VECTOR_ADD_RID]);;

let LEAST_SQUARE_GENERAL_SOLUTION_ALT = prove
    (`!A:real^N^M y. (?x. A ** x = y ==> (?z. x = matrix_inv A ** y + (mat 1 - matrix_inv A ** A) ** z)) /\ 
    (!z x. (?x. A ** x = y) /\ x = matrix_inv A ** y + (mat 1 - matrix_inv A ** A) ** z ==> A ** x = y)`,
    REPEAT GEN_TAC THEN CONJ_TAC THENL
    [EXISTS_TAC `x:real^N` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN 
     EXISTS_TAC `x:real^N` THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID] THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[LEAST_SQUARE_HAS_SOLUTION;MATRIX_VECTOR_MUL_ADD_LDISTRIB;MATRIX_VECTOR_MUL_ASSOC;MATRIX_SUB_LDISTRIB;MATRIX_MUL_RID;MATRIX_INV_MUL_INNER] THEN
    SIMP_TAC[MATRIX_SUB_REFL;MATRIX_VECTOR_MUL_LZERO;VECTOR_ADD_RID]);;

let MSUM_MATRIX_VECTOR_MUL = prove  
   (`!f:num->real^N^M x:real^N s. 
        FINITE s ==> (msum s f) ** x = vsum s (\A. f(A) ** x)`,
    GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN 
    SIMP_TAC[MSUM_CLAUSES;VSUM_CLAUSES;MATRIX_VECTOR_MUL_LZERO;MATRIX_VECTOR_MUL_ADD_RDISTRIB]);;
   
let LEAST_SQUARE_N = prove
    (`!n A:num->real^N^M B:num->real^M X:real^N.
        (!i. 1 <= i /\ i <= n ==> A(i) ** X = B(i)) /\
        invertible(msum (1..n) (\i. transp(A(i)) ** A(i))) ==> 
         X = matrix_inv(msum (1..n) (\i. transp(A(i)) ** A(i))) ** (vsum (1..n) (\i. transp(A(i)) ** B(i)))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `msum (1..n) (\i. transp((A:num->real^N^M)(i)) ** A(i)) ** (X:real^N) = vsum (1..n) (\i. transp(A(i)) ** B(i))` ASSUME_TAC THENL
    [SIMP_TAC[FINITE_NUMSEG;MSUM_MATRIX_VECTOR_MUL] THEN
     MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
     ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC];ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_INV;MATRIX_VECTOR_MUL_LID]);;

let PARALLEL_CONDITION = prove
    (`!v A f. ((!i. 1 <= i /\ i <= 2 ==> f i = vec3_2_ssm(v i)) /\ 
        A = pastecart (f(1)) (f(2))) ==> 
        (v(1) cross v(2) = vec 0 <=> ~(invertible(transp(A) ** A)))`,    
    SIMP_TAC[FORALL_2;GSYM DET_EQ_0] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC[pastecart;LAMBDA_BETA;DIMINDEX_FINITE_SUM;TRANSP_COMPONENT;matrix_mul;DET_3;DIMINDEX_3;SUM_6;ARITH_RULE `3 + 3 = 6`;LE_REFL;ARITH_RULE `1 <= 2 /\ 1 <= 3 /\ 2 <= 3`;ARITH_RULE `~(4 <= 3) /\ ~(5 <= 3) /\ ~(6 <= 3)`;ARITH_RULE `4 - 3 = 1 /\ 5 - 3 = 2 /\ 6 - 3 = 3`;vec3_2_ssm;VECTOR_3;VECTOR_NEG_COMPONENT] THEN
    SIMP_TAC[REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_NEG_NEG;REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_NEG_0;GSYM REAL_NEG_ADD] THEN
    SIMP_TAC[cross;CART_EQ;LAMBDA_BETA;VEC_COMPONENT;VECTOR_3;DIMINDEX_3;FORALL_3] THEN
    ABBREV_TAC `x1 = ((v 1):real^3)$1` THEN 
    ABBREV_TAC `x2 = ((v 2):real^3)$1` THEN 
    ABBREV_TAC `y1 = ((v 1):real^3)$2` THEN 
    ABBREV_TAC `y2 = ((v 2):real^3)$2` THEN 
    ABBREV_TAC `z1 = ((v 1):real^3)$3` THEN 
    ABBREV_TAC `z2 = ((v 2):real^3)$3` THEN 
    SIMP_TAC[REAL_ARITH `(z1 * z1 + y1 * y1 + z2 * z2 + y2 * y2) *
            (z1 * z1 + x1 * x1 + z2 * z2 + x2 * x2) *
            (y1 * y1 + x1 * x1 + y2 * y2 + x2 * x2) +
            --((y1 * x1 + y2 * x2) * (z1 * y1 + z2 * y2) * (x1 * z1 + x2 * z2)) +
            --((z1 * x1 + z2 * x2) * (x1 * y1 + x2 * y2) * (y1 * z1 + y2 * z2)) -
            (z1 * z1 + y1 * y1 + z2 * z2 + y2 * y2) * (z1 * y1 + z2 * y2) * (y1 * z1 + y2 * z2) -
            (y1 * x1 + y2 * x2) * (x1 * y1 + x2 * y2) * (y1 * y1 + x1 * x1 + y2 * y2 + x2 * x2) -
            (z1 * x1 + z2 * x2) * (z1 * z1 + x1 * x1 + z2 * z2 + x2 * x2) * (x1 * z1 + x2 * z2) = 
            (x1 pow 2 + x2 pow 2 + y1 pow 2 + y2 pow 2 + z1 pow 2 + z2 pow 2) * 
            ((x1 * y2 - y1 * x2) pow 2 + (z1 * x2 - x1 * z2) pow 2 + (y1 * z2 - z1 * y2) pow 2)`] THEN
    SIMP_TAC[REAL_ENTIRE] THEN
    EQ_TAC THENL
    [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ARITH `a1 + a2 + a3 + a4 + a5 + a6 = (a1 + a2) + (a3 + a4) + (a5 + a6)`] THEN
    SIMP_TAC[REAL_ARITH `&0 <= a /\ &0 <= b ==> (a + b = &0 <=> a = &0 /\ b = &0)`;REAL_ADD_ASSOC;REAL_LE_ADD;REAL_POW_2;REAL_LE_SQUARE;REAL_FIELD `x * x = &0 <=> x = &0`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO;REAL_SUB_RZERO]);;
    
let NOT_PARALLEL_CONDITION = prove
    (`!v A f. ((!i. 1 <= i /\ i <= 2 ==> f i = vec3_2_ssm(v i)) /\ 
        A = pastecart (f(1)) (f(2))) ==> 
        (~(v(1) cross v(2) = vec 0) <=> invertible(transp(A) ** A))`,
    MESON_TAC[PARALLEL_CONDITION]);;
    
let LEAST_SQUARE_DET_TRANSP_MUL = prove
    (`!v A f. ((!i. 1 <= i /\ i <= 2 ==> f i = vec3_2_ssm(v i)) /\ 
        A = pastecart (f(1)) (f(2))) ==> 
        det(transp(A) ** A) = (norm(v 1) pow 2 + norm (v 2) pow 2) * (norm((v 1) cross (v 2)) pow 2)`,
    SIMP_TAC[FORALL_2] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC[pastecart;LAMBDA_BETA;DIMINDEX_FINITE_SUM;TRANSP_COMPONENT;matrix_mul;DET_3;DIMINDEX_3;SUM_6;ARITH_RULE `3 + 3 = 6`;LE_REFL;ARITH_RULE `1 <= 2 /\ 1 <= 3 /\ 2 <= 3`;ARITH_RULE `~(4 <= 3) /\ ~(5 <= 3) /\ ~(6 <= 3)`;ARITH_RULE `4 - 3 = 1 /\ 5 - 3 = 2 /\ 6 - 3 = 3`;vec3_2_ssm;VECTOR_3;VECTOR_NEG_COMPONENT] THEN
    SIMP_TAC[REAL_MUL_LNEG;REAL_MUL_RNEG;REAL_NEG_NEG;REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_NEG_0;GSYM REAL_NEG_ADD] THEN
    SIMP_TAC[DOT_3;NORM_POW_2;cross;LAMBDA_BETA;VEC_COMPONENT;VECTOR_3;DIMINDEX_3;FORALL_3] THEN
    ARITH_TAC);;
    
let COFACTOR_3 = prove
    (`!A:real^3^3. cofactor A = vector[vector[(A$2$2 * A$3$3 - A$2$3 * A$3$2);
                                        --(A$2$1 * A$3$3 - A$2$3 * A$3$1);
                                        (A$2$1 * A$3$2 - A$2$2 * A$3$1)];
                                        vector[--(A$1$2 * A$3$3 - A$1$3 * A$3$2);
                                        (A$1$1 * A$3$3 - A$1$3 * A$3$1);
                                        --(A$1$1 * A$3$2 - A$1$2 * A$3$1)];
                                        vector[(A$1$2 * A$2$3 - A$1$3 * A$2$2);
                                        --(A$1$1 * A$2$3 - A$1$3 * A$2$1);
                                        (A$1$1 * A$2$2 - A$1$2 * A$2$1)]]:real^3^3`,
    SIMP_TAC[cofactor;CART_EQ;LAMBDA_BETA;DET_3;DIMINDEX_3;FORALL_3;VECTOR_3;ARITH_RULE `1 <= 2 /\ 1 <= 3 /\ 2 <= 3`;LE_REFL;ARITH_EQ] THEN
    SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID;REAL_SUB_LZERO;REAL_SUB_RZERO;REAL_NEG_0;REAL_ADD_RID;REAL_ADD_LID] THEN
    ARITH_TAC);;

let LEAST_SQUARE = prove
    (`!v:num->real^3 A B X:real^3 f.
        (!i. 1 <= i /\ i <= 2 ==> f i = vec3_2_ssm (v i)) /\
         A = pastecart (f(1)) (f(2)) /\ ~(v(1) cross v(2) = vec 0) /\ A ** X = B ==> 
         X = matrix_inv(transp(A) ** A) ** transp(A) ** B`,
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
   SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;GSYM MATRIX_MUL_ASSOC] THEN
   SUBGOAL_THEN `invertible(transp A ** (A:real^3^(3,3)finite_sum))` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_PARALLEL_CONDITION];ALL_TAC] THEN
   ASM_SIMP_TAC[MATRIX_INV;MATRIX_VECTOR_MUL_LID]);;
   
let LEAST_SQUARE_ALT = prove
    (`!v A B X:real^3 f. (!i. 1 <= i /\ i <= 2 ==> f i = vec3_2_ssm (v i)) /\
         A = pastecart (f(1)) (f(2))  /\ ~(v(1) cross v(2) = vec 0) /\ A ** X = B ==> 
         X = inv((norm(v 1) pow 2 + norm (v 2) pow 2) * (norm((v 1) cross (v 2)) pow 2)) %% cofactor(transp A ** A) ** transp(A) ** B`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `invertible(transp A ** (A:real^3^(3,3)finite_sum))` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_PARALLEL_CONDITION];ALL_TAC] THEN
    MP_TAC (ISPECL[`v:num->real^3`;`A:real^3^(3,3)finite_sum`;`B:real^(3,3)finite_sum`;`X:real^3`;`f:num->real^3^3`] LEAST_SQUARE) THEN
    ASM_SIMP_TAC[GSYM INVERTIBLE_DET_NZ;MATRIX_INV_COFACTOR;GSYM COFACTOR_TRANSP;TRANSP_TRANSP;MATRIX_TRANSP_MUL] THEN
    ASM_MESON_TAC[LEAST_SQUARE_DET_TRANSP_MUL]);;

let PASTECART_MATRIX_VECTOR_MUL = prove
    (`!A1:real^N^M A2:real^N^P X:real^N B1:real^M B2:real^P. 
        (pastecart A1 A2) ** X = pastecart B1 B2 <=> A1 ** X = B1 /\ A2 ** X = B2`,
    REPEAT GEN_TAC THEN
    SIMP_TAC[pastecart;matrix_vector_mul;CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM] THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= M + P <=> (1 <= i /\ i <= M) \/ (1 <= (i - M) /\ (i - M) <= P)`] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`);
     FIRST_X_ASSUM(MP_TAC o SPEC `i + dimindex(:M)`);
     FIRST_X_ASSUM(MP_TAC o SPEC `i - dimindex(:M)`) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`);
     FIRST_X_ASSUM(MP_TAC o SPEC `i - dimindex(:M)`)] THEN
    ASM_SIMP_TAC[ADD_SUB] THEN ASM_ARITH_TAC);; 
    
let TRANSP_PASTECART_MATRIX_MUL = prove
    (`!A1:real^N^M A2:real^N^P X:real^N B1:real^Q^M B2:real^Q^P. 
        transp(pastecart A1 A2) ** pastecart B1 B2 = transp A1 ** B1 + transp A2 ** B2`,
    SIMP_TAC[pastecart;matrix_mul;CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM;TRANSP_COMPONENT;MATRIX_ADD_COMPONENT] THEN
    SIMP_TAC[ARITH_RULE `1 <= m + 1`;SUM_ADD_SPLIT;REAL_EQ_ADD_LCANCEL] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC[COND_RATOR;COND_RAND] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC [`(\i. i - dimindex(:M))`;`(\i. i + dimindex(:M))`] THEN
    SIMP_TAC[IN_NUMSEG] THEN ARITH_TAC);; 
    
let TRANSP_PASTECART_MATRIX_VECTOR_MUL = prove
    (`!A1:real^N^M A2:real^N^P X:real^N B1:real^M B2:real^P. 
        transp(pastecart A1 A2) ** pastecart B1 B2 = transp A1 ** B1 + transp A2 ** B2`,
    SIMP_TAC[pastecart;matrix_vector_mul;CART_EQ;LAMBDA_BETA;DIMINDEX_FINITE_SUM;TRANSP_COMPONENT;VECTOR_ADD_COMPONENT] THEN
    SIMP_TAC[ARITH_RULE `1 <= m + 1`;SUM_ADD_SPLIT;REAL_EQ_ADD_LCANCEL] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC[COND_RATOR;COND_RAND] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC [`(\i. i - dimindex(:M))`;`(\i. i + dimindex(:M))`] THEN
    SIMP_TAC[IN_NUMSEG] THEN ARITH_TAC);;
  
(* ------------------------------------------------------------------------- *)
(* The general or special solution                                           *)
(* ------------------------------------------------------------------------- *)
  
let SOLUTION_RODRIGUES_PARAMETER = prove
    (`!w:real^3 v a:real A B X f g. 
        (norm w = &1) /\ ~(cos (a * inv (&2)) = &0) /\
        (!i. 1 <= i /\ i <= 2 ==>  f i = (v i) + (rotate_vector a w (v i)) /\
                                    g i = (v i) - (rotate_vector a w (v i))) /\
        ~(f(1) cross f(2) = vec 0) /\
        A = pastecart (vec3_2_ssm(f(1))) (vec3_2_ssm(f(2))) /\
        B = pastecart (g(1)) (g(2)) /\
        X = (rodrigues_parameter a w) ==>
        X = matrix_inv(transp(A) ** A) ** transp(A) ** B`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(A:real^3^(3,3)finite_sum) ** (X:real^3) = B` ASSUME_TAC THENL
    [ASM_SIMP_TAC[PASTECART_MATRIX_VECTOR_MUL] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FORALL_2]) THEN
     ASM_SIMP_TAC[ROTATION_RELATION_RODRIGUES_PARAMETER]
     ;ALL_TAC] THEN
    MP_TAC (ISPECL[`f:num->real^3`;`A:real^3^(3,3)finite_sum`;`B:real^(3,3)finite_sum`;`X:real^3`;`(\i. vec3_2_ssm(f(i))):num->real^3^3`] LEAST_SQUARE) THEN
    ASM_SIMP_TAC[]);;
    
let SOLUTION_RODRIGUES_PARAMETER_ALT = prove
    (`!w:real^3 v a:real A B X f g. 
        (norm w = &1) /\ ~(cos (a * inv (&2)) = &0) /\
        (!i. 1 <= i /\ i <= 2 ==>  f i = (v i) + (rotate_vector a w (v i)) /\
                                    g i = (v i) - (rotate_vector a w (v i))) /\
        ~(f(1) cross f(2) = vec 0) /\
        A = pastecart (vec3_2_ssm(f(1))) (vec3_2_ssm(f(2))) /\
        B = pastecart (g(1)) (g(2)) /\
        X = (rodrigues_parameter a w) ==>
        X = inv((norm(f 1) pow 2 + norm (f 2) pow 2) * (norm((f 1) cross (f 2)) pow 2)) %% cofactor(transp A ** A) ** transp(A) ** B`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(A:real^3^(3,3)finite_sum) ** (X:real^3) = B` ASSUME_TAC THENL
    [ASM_SIMP_TAC[PASTECART_MATRIX_VECTOR_MUL] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FORALL_2]) THEN
     ASM_SIMP_TAC[ROTATION_RELATION_RODRIGUES_PARAMETER]
     ;ALL_TAC] THEN
    MP_TAC (ISPECL[`f:num->real^3`;`A:real^3^(3,3)finite_sum`;`B:real^(3,3)finite_sum`;`X:real^3`;`(\i. vec3_2_ssm(f(i))):num->real^3^3`] LEAST_SQUARE_ALT) THEN
    ASM_SIMP_TAC[]);;

let MATRIX_VECTOR_MUL_LCANCEL = prove
 (`!A:real^M^N b:real^M c.
        invertible A ==> (A ** b = A ** c <=> b = c)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `matrix_vector_mul (matrix_inv(A:real^M^N)):real^N->real^M`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

let MATRIX_VECTOR_MUL_RCANCEL = prove
 (`!a b:real^M C:real^P^M.
        invertible C ==> (a ** C = b ** C <=> a = b)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  EQ_TAC THEN SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM TRANSP_TRANSP] THEN
  SIMP_TAC[GSYM MATRIX_VECTOR_MUL_TRANSP] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `matrix_vector_mul (matrix_inv(transp (C:real^P^M))):real^P->real^M`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_INV_TRANSP;GSYM MATRIX_TRANSP_MUL;MATRIX_VECTOR_MUL_LID;TRANSP_MAT]);;
  
let GENERAL_SOLUTION_RODRIGUES_PARAMETER = prove
    (`!w:real^3 v a:real A B X f g. 
        (norm w = &1) /\ ~(cos (a * inv (&2)) = &0) /\
        (!i. 1 <= i /\ i <= 2 ==>  f i = (v i) + (rotate_vector a w (v i)) /\
                                    g i = (v i) - (rotate_vector a w (v i))) /\
        A = pastecart (vec3_2_ssm(f(1))) (vec3_2_ssm(f(2))) /\
        B = pastecart (g(1)) (g(2)) /\
        X = (rodrigues_parameter a w) ==>
        (?z. X = matrix_inv A ** B + (mat 1 - matrix_inv A ** A) ** z)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(A:real^3^(3,3)finite_sum) ** (X:real^3) = B` ASSUME_TAC THENL
    [ASM_SIMP_TAC[PASTECART_MATRIX_VECTOR_MUL] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FORALL_2]) THEN
     ASM_SIMP_TAC[ROTATION_RELATION_RODRIGUES_PARAMETER]
     ;ALL_TAC] THEN
    SUBGOAL_THEN `(A:real^3^(3,3)finite_sum) ** matrix_inv A ** B = B` MP_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
     SIMP_TAC[GSYM MATRIX_MUL_ASSOC;MATRIX_INV_MUL_INNER];ALL_TAC] THEN
     SIMP_TAC[GSYM LEAST_SQUARE_HAS_SOLUTION] THEN
     ASM_MESON_TAC[LEAST_SQUARE_GENERAL_SOLUTION]);;
 
let IS_GENERAL_SOLUTION_RODRIGUES_PARAMETER = prove
    (`!w:real^3 v v' a:real A B f g. 
        (norm w = &1) /\ ~(cos (a * inv (&2)) = &0) /\
        (!i. 1 <= i /\ i <= 2 ==>  f i = (v i) + (v' i) /\
                                    g i = (v i) - (v' i)) /\
        A = pastecart (vec3_2_ssm(f(1))) (vec3_2_ssm(f(2))) /\
        B = pastecart (g(1)) (g(2)) /\
        A ** matrix_inv A ** B = B /\
        (!z. rodrigues_parameter a w = matrix_inv A ** B + (mat 1 - matrix_inv A ** A) ** z) ==>
       (!i. 1 <= i /\ i <= 2 ==> v' i = rotate_vector a w (v i))`,
    let lem = MESON [INVERTIBLE_MAT_SUB_SSM;MATRIX_VECTOR_MUL_LCANCEL;EQ_SYM_EQ] `b = c <=> (mat 1 - vec3_2_ssm (rodrigues_parameter a w)) ** b = (mat 1 - vec3_2_ssm (rodrigues_parameter a w)) ** c` in
    SIMP_TAC[FORALL_2] THEN REPEAT GEN_TAC THEN
    SIMP_TAC[GSYM CONJ_ASSOC;GSYM LEAST_SQUARE_HAS_SOLUTION] THEN
    INTRO_TAC "norm cos f1 g1 f2 g2 Af Bg hs r" THEN
    ASM_SIMP_TAC[rotate_vector;RODRIGUES_FORMULA_CAYLEY] THEN
    SIMP_TAC[MATRIX_TRANSP_MUL;GSYM MATRIX_INV_TRANSP;VEC3_SSM_TRANSP_SUB;VEC3_SSM_TRANSP_ADD] THEN 
    ONCE_REWRITE_TAC[lem] THEN
    SIMP_TAC[INVERTIBLE_MAT_SUB_SSM;MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC;MATRIX_INV;MATRIX_MUL_LID] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID] THEN
    SIMP_TAC[VECTOR_ARITH `(c - d:real^N = a + b) <=> (--(b + d) = a - c)`;GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
    SIMP_TAC[GSYM CROSS_SSM] THEN
    ONCE_REWRITE_TAC[CROSS_SKEW] THEN
    SIMP_TAC[VECTOR_NEG_NEG;CROSS_SSM;GSYM PASTECART_MATRIX_VECTOR_MUL] THEN
    REMOVE_THEN "f1" (SUBST1_TAC o SYM) THEN REMOVE_THEN "f2" (SUBST1_TAC o SYM) THEN
    REMOVE_THEN "g1" (SUBST1_TAC o SYM) THEN REMOVE_THEN "g2" (SUBST1_TAC o SYM) THEN
    REMOVE_THEN "Af" (SUBST1_TAC o SYM) THEN REMOVE_THEN "Bg" (SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[LEAST_SQUARE_GENERAL_SOLUTION_ALT]);;

let IS_UNIQUE_SOLUTION_RODRIGUES_PARAMETER = prove
    (`!w:real^3 v v' a:real A B f g. 
        (norm w = &1) /\ ~(cos (a * inv (&2)) = &0) /\
        (!i. 1 <= i /\ i <= 2 ==>  f i = (v i) + (v' i) /\
                                    g i = (v i) - (v' i)) /\
        ~(f(1) cross f(2) = vec 0) /\
        A = pastecart (vec3_2_ssm(f(1))) (vec3_2_ssm(f(2))) /\
        B = pastecart (g(1)) (g(2)) /\
        A ** matrix_inv A ** B = B /\
        rodrigues_parameter a w = matrix_inv(transp(A) ** A) ** transp(A) ** B ==>
       (!i. 1 <= i /\ i <= 2 ==> v' i = rotate_vector a w (v i))`,
    let lem = MESON [INVERTIBLE_MAT_SUB_SSM;MATRIX_VECTOR_MUL_LCANCEL;EQ_SYM_EQ] `b = c <=> (mat 1 - vec3_2_ssm (rodrigues_parameter a w)) ** b = (mat 1 - vec3_2_ssm (rodrigues_parameter a w)) ** c` in
    SIMP_TAC[FORALL_2] THEN REPEAT GEN_TAC THEN SIMP_TAC[GSYM CONJ_ASSOC] THEN
    INTRO_TAC "norm cos f1 g1 f2 g2 crnz Af Bg hs r" THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM) THEN
    ASM_SIMP_TAC[rotate_vector;RODRIGUES_FORMULA_CAYLEY] THEN
    SIMP_TAC[MATRIX_TRANSP_MUL;GSYM MATRIX_INV_TRANSP;VEC3_SSM_TRANSP_SUB;VEC3_SSM_TRANSP_ADD] THEN 
    ONCE_REWRITE_TAC[lem] THEN
    SIMP_TAC[INVERTIBLE_MAT_SUB_SSM;MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC;MATRIX_INV;MATRIX_MUL_LID] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB;MATRIX_VECTOR_MUL_SUB_RDISTRIB;MATRIX_VECTOR_MUL_LID] THEN
    SIMP_TAC[VECTOR_ARITH `(c - d:real^N = a + b) <=> (--(b + d) = a - c)`;GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
    SIMP_TAC[GSYM CROSS_SSM] THEN
    ONCE_REWRITE_TAC[CROSS_SKEW] THEN
    SIMP_TAC[VECTOR_NEG_NEG;CROSS_SSM;GSYM PASTECART_MATRIX_VECTOR_MUL] THEN
    REMOVE_THEN "f1" (SUBST1_TAC o SYM) THEN REMOVE_THEN "f2" (SUBST1_TAC o SYM) THEN
    REMOVE_THEN "g1" (SUBST1_TAC o SYM) THEN REMOVE_THEN "g2" (SUBST1_TAC o SYM) THEN
    REMOVE_THEN "Af" (SUBST1_TAC o SYM) THEN REMOVE_THEN "Bg" (SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SIMP_TAC[MATRIX_INV_COVARIANCE] THEN
    SIMP_TAC[(MESON [MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_ASSOC] `!A:real^N^M B:real^P^N C:real^Q^P D:real^K^Q x:real^K. A ** (B ** C) ** D ** x = (A ** B ** C ** D) ** x`)] THEN
    SIMP_TAC[GSYM MATRIX_TRANSP_MUL;MATRIX_INV_MUL_OUTER;(REWRITE_RULE [symmetric_matrix] SYMMETRIC_MATRIX_INV_RMUL)] THEN
    ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC]);;
    
 
