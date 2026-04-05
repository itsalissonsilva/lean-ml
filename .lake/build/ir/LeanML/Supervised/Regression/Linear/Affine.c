// Lean compiler output
// Module: LeanML.Supervised.Regression.Linear.Affine
// Imports: public import Init public import LeanML.Optimization public import Mathlib.Analysis.InnerProductSpace.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LeanML_LeanML_Supervised_Regression_Linear_Affine_predict___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanML_LeanML_Supervised_Regression_Linear_Affine_predict(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanML_LeanML_Supervised_Regression_Linear_Affine_predict___redArg(lean_object* v_inst_1_, lean_object* v_m_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_toCommRing_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_toMul_8_; lean_object* v_toAdd_9_; lean_object* v_w_10_; lean_object* v_b_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_toCommRing_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toCommRing_4_);
lean_dec_ref(v_inst_1_);
v___x_5_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_4_);
v___x_6_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_5_);
v___x_7_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_6_);
v_toMul_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_toMul_8_);
v_toAdd_9_ = lean_ctor_get(v___x_7_, 1);
lean_inc(v_toAdd_9_);
lean_dec_ref(v___x_7_);
v_w_10_ = lean_ctor_get(v_m_2_, 0);
lean_inc(v_w_10_);
v_b_11_ = lean_ctor_get(v_m_2_, 1);
lean_inc(v_b_11_);
lean_dec_ref(v_m_2_);
v___x_12_ = lean_apply_2(v_toMul_8_, v_w_10_, v_x_3_);
v___x_13_ = lean_apply_2(v_toAdd_9_, v___x_12_, v_b_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_LeanML_LeanML_Supervised_Regression_Linear_Affine_predict(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_m_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_LeanML_LeanML_Supervised_Regression_Linear_Affine_predict___redArg(v_inst_15_, v_m_16_, v_x_17_);
return v___x_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_LeanML_LeanML_Optimization(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanML_LeanML_Supervised_Regression_Linear_Affine(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanML_LeanML_Optimization(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
