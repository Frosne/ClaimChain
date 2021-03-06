/* This file was auto-generated by KreMLin! */

#include "Hacl_VRF_Hash.h"

bool Hacl_VRF_Hash__ECVRF_prove_2(uint8_t *proof, uint8_t *secret)
{
  uint64_t buf[30U] = { 0U };
  uint64_t *cf = buf;
  uint64_t *xf = buf + (uint32_t)5U;
  uint64_t *cxf = buf + (uint32_t)10U;
  uint64_t *kf = buf + (uint32_t)15U;
  uint8_t *c = proof + (uint32_t)32U;
  uint8_t *s = proof + (uint32_t)48U;
  uint8_t *clow = proof + (uint32_t)48U;
  uint8_t *chigh = proof + (uint32_t)32U;
  uint8_t *privateKey = secret;
  uint8_t *random = secret + (uint32_t)32U;
  Hacl_VRF_Lib_fexpand(cf, c);
  Hacl_VRF_Lib_fexpand(xf, privateKey);
  Hacl_VRF_Lib_fexpand(kf, random);
  Hacl_VRF_Lib_fmul(cxf, cf, xf);
  Hacl_VRF_Lib_fdifference_reduced(kf, cxf);
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i = i + (uint32_t)1U)
  {
    uint8_t src_i = clow[i];
    chigh[i] = src_i;
  }
  Hacl_VRF_Lib_fcontract(s, kf);
  bool r = true;
  return r;
}

bool
Hacl_VRF_Hash__ECVRF_prove(
  Prims_nat len,
  uint8_t *proof,
  uint32_t inputLength,
  uint8_t *input,
  uint8_t *secret,
  uint64_t *pk
)
{
  uint64_t buf[120U] = { 0U };
  uint8_t *c = proof + (uint32_t)32U;
  uint8_t *privateKey = secret;
  uint8_t *random = secret + (uint32_t)32U;
  uint64_t *generator = buf;
  Hacl_VRF_Lib_make_g(generator);
  uint64_t *h = buf + (uint32_t)20U;
  bool r0 = Hacl_VRF_HashToCurveFinal__ECVRF_hash_to_curve(len, h, pk, inputLength, input);
  bool r;
  if (!r0)
    r = false;
  else
  {
    uint64_t *publicKey = buf + (uint32_t)40U;
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)20U; i = i + (uint32_t)1U)
    {
      uint64_t src_i = pk[i];
      publicKey[i] = src_i;
    }
    uint64_t *gammaPoint = buf + (uint32_t)60U;
    Hacl_VRF_Lib_point_mult(gammaPoint, h, privateKey);
    uint64_t *gk = buf + (uint32_t)80U;
    Hacl_VRF_Lib_point_mult(gk, generator, random);
    uint64_t *hk = buf + (uint32_t)100U;
    Hacl_VRF_Lib_point_mult(hk, h, random);
    Hacl_VRF_HashPoints__ECVRF_hashPoints(c, buf);
    r = true;
  }
  bool r1 = r;
  if (!r1)
    return false;
  else
    return Hacl_VRF_Hash__ECVRF_prove_2(proof, secret);
}

