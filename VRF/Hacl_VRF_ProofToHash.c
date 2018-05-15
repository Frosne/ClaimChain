/* This file was auto-generated by KreMLin! */

#include "Hacl_VRF_ProofToHash.h"

bool Hacl_VRF_ProofToHash_partialDecodeProof(uint64_t *gamma, uint8_t *proof)
{
  uint8_t *gamma_ = proof;
  bool valid = Hacl_VRF_Lib_decompress(gamma, gamma_);
  if (!valid)
    return false;
  else
    return true;
}

bool Hacl_VRF_ProofToHash_proofToHash(uint8_t *beta, uint8_t *proof)
{
  uint64_t buf[20U] = { 0U };
  bool r0 = Hacl_VRF_ProofToHash_partialDecodeProof(buf, proof);
  bool r;
  if (!r0)
    r = false;
  else
  {
    Hacl_VRF_HashToCurveFinal_pointMult8(buf, buf);
    uint32_t sizeHash = (uint32_t)32U;
    KRML_CHECK_SIZE((uint8_t)0U, sizeHash);
    uint8_t buf1[sizeHash];
    memset(buf1, 0U, sizeHash * sizeof buf1[0U]);
    uint8_t *bT = buf1;
    Hacl_VRF_Lib_compress(bT, buf);
    Hacl_VRF_Lib_hash(beta, (uint32_t)32U, buf1);
    bool r1 = true;
    r = r1;
  }
  return r;
}

