/* This file was auto-generated by KreMLin! */

#include "Hacl_VRF_DecodeProof.h"

bool Hacl_VRF_DecodeProof_decodeProof(uint64_t *gamma, uint8_t *c, uint8_t *s, uint8_t *proof)
{
  uint8_t *gamma_ = proof;
  uint8_t *c_ = proof + (uint32_t)32U;
  uint8_t *s_ = proof + (uint32_t)48U;
  bool valid = Hacl_VRF_Lib_decompress(gamma, gamma_);
  if (!valid)
    return false;
  else
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
    {
      uint8_t src_i = c_[i];
      c[i] = src_i;
    }
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
    {
      uint8_t src_i = s_[i];
      s[i] = src_i;
    }
    return true;
  }
}
