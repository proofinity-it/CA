#include <lean/lean.h>
#include <openssl/evp.h>
#include <string.h>

LEAN_EXPORT lean_obj_res lean_sha256_hash(b_lean_obj_arg data, lean_obj_arg world) {
    size_t len = lean_sarray_size(data);
    const uint8_t *buf = lean_sarray_cptr(data);
    unsigned char hash[32];
    unsigned int hash_len = 32;

    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx, EVP_sha256(), NULL);
    EVP_DigestUpdate(ctx, buf, len);
    EVP_DigestFinal_ex(ctx, hash, &hash_len);
    EVP_MD_CTX_free(ctx);

    lean_object *result = lean_alloc_sarray(1, 32, 32);
    memcpy(lean_sarray_cptr(result), hash, 32);
    return lean_io_result_mk_ok(result);
}
