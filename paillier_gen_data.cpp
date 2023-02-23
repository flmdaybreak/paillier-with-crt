#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <cstring>
#include <gmp.h>
#include <vector>
#include <ctime>
#include <cassert>
#include <random>
#include <utility> 
#include <tuple>
#include <time.h>
#include <fstream>
#include <iostream>
#include <sstream>

gmp_randstate_t randomGeneratorState;
unsigned long randomSeed;
using namespace std;

struct PubKey
{
    mpz_t n;
    mpz_t g;
    mpz_t nSquared;
};

#define SK_L_SIZE 6
#define SK_H_SIZE 6
struct PrivKey
{   
    //n_length / 2
    mpz_t p;
    mpz_t q;
    mpz_t pMinusOne;
    mpz_t qMinusOne;
    mpz_t hp;
    mpz_t hq;
    
    //nlength
    mpz_t n;
    mpz_t pSquared;
    mpz_t qSquared;
    mpz_t qTimesQInvModP;
    mpz_t pTimesPInvModQ;
    mpz_t posNegBoundary;
};

void initPubKey(struct PubKey *pubKey)
{
    mpz_init(pubKey->n);
    mpz_init(pubKey->g);
    mpz_init(pubKey->nSquared);
}

void freePubKey(struct PubKey *pubKey)
{
    mpz_clear(pubKey->n);
    mpz_clear(pubKey->nSquared);
    mpz_clear(pubKey->g);
}

void initPrivKey(struct PrivKey *privKey)
{
    mpz_init(privKey->p);
    mpz_init(privKey->q);
    mpz_init(privKey->pMinusOne);
    mpz_init(privKey->qMinusOne);
    mpz_init(privKey->hp);
    mpz_init(privKey->hq);

    mpz_init(privKey->n);
    mpz_init(privKey->pSquared);
    mpz_init(privKey->qSquared);
    mpz_init(privKey->qTimesQInvModP);
    mpz_init(privKey->pTimesPInvModQ);
    mpz_init(privKey->posNegBoundary);
}

void freePrivKey(struct PrivKey *privKey)
{
    mpz_clear(privKey->p);
    mpz_clear(privKey->q);
    mpz_clear(privKey->pMinusOne);// useful or useless 
    mpz_clear(privKey->qMinusOne);// useful or useless 
    mpz_clear(privKey->hp);
    mpz_clear(privKey->hq);

    mpz_clear(privKey->n);    
    mpz_clear(privKey->pSquared);
    mpz_clear(privKey->qSquared);
    mpz_clear(privKey->qTimesQInvModP);
    mpz_clear(privKey->pTimesPInvModQ);
    mpz_clear(privKey->posNegBoundary);// useful or useless 
}

unsigned long getRandomSeed()
{
    FILE *urandom;
    unsigned long randomNumber;

    urandom = fopen("/dev/urandom", "r");

    if (urandom == NULL)
    {
        fprintf(stderr, "Cannot open /dev/urandom!\n");
        exit(1);
    }

    fread(&randomNumber, sizeof(randomNumber), 1, urandom);

    return randomNumber;
}

void getRandomPrime(mpz_t output, unsigned long primeLen)
{
    do
    {
        //generate a random number in the interval [0, 2^(numberOfBits - 1))
        mpz_urandomb(output, randomGeneratorState, primeLen - 1);

        //shift number to the interval [2^(numberOfBits - 1), 2^numberOfBits)
        mpz_setbit(output, primeLen - 1);
    }
    while (!mpz_probab_prime_p(output, 10));
}

void print(mpz_t input)
{
    unsigned int base = 10;

    //get a pointer to GMP's internal memory deallocator function
    void (*deallocator)(void *, size_t);
    mp_get_memory_functions(NULL, NULL, &deallocator);

    //get the string representation of input
    char *data = mpz_get_str(NULL, base, input);

    printf("%s\n", data);

    (*deallocator)((void *)data, strlen(data));
}

//Computes @f$ L(u) = \frac{u - 1}{d} @f$
void L(mpz_t output, mpz_t input, mpz_t d)
{
    mpz_sub_ui(output, input, 1);

    mpz_tdiv_q(output, output, d);
}

void generateKeys(struct PubKey *pubKey, struct PrivKey *privKey,  unsigned long n_length)
{
    // unsigned long keyLen = 2048;
    unsigned long primeLen = n_length / 2;

    mpz_t tmp;
    mpz_init(tmp);

    do
    {
        getRandomPrime(privKey->p, primeLen);
        getRandomPrime(privKey->q, primeLen);

        while (!mpz_cmp(privKey->p, privKey->q))
        {
            getRandomPrime(privKey->p, primeLen);
        }

        mpz_mul(pubKey->n, privKey->p, privKey->q);
    }
    while (mpz_sizeinbase(pubKey->n, 2) != n_length);

    mpz_mul(pubKey->nSquared, pubKey->n, pubKey->n);

    mpz_add_ui(pubKey->g, pubKey->n, 1);
    mpz_set(privKey->n, pubKey->n);

    mpz_sub_ui(privKey->pMinusOne, privKey->p, 1);
    mpz_sub_ui(privKey->qMinusOne, privKey->q, 1);

    mpz_mul(privKey->pSquared, privKey->p, privKey->p);
    mpz_mul(privKey->qSquared, privKey->q, privKey->q);

    //compute hp
    mpz_powm(tmp, pubKey->g, privKey->pMinusOne, privKey->pSquared);
    L(privKey->hp, tmp, privKey->p);
    mpz_invert(privKey->hp, privKey->hp, privKey->p);

    //compute hq
    mpz_powm(tmp, pubKey->g, privKey->qMinusOne, privKey->qSquared);
    L(privKey->hq, tmp, privKey->q);
    mpz_invert(privKey->hq, privKey->hq, privKey->q);

    //precomputations
    mpz_invert(tmp, privKey->p, privKey->q);
    mpz_mul(privKey->pTimesPInvModQ, privKey->p, tmp);
    mpz_invert(tmp, privKey->q, privKey->p);
    mpz_mul(privKey->qTimesQInvModP, privKey->q, tmp);

    mpz_tdiv_q_ui(privKey->posNegBoundary, pubKey->n, 2);

    mpz_clear(tmp);
}

void encrypt_ul(mpz_t output, long input, struct PubKey *pubKey)
{
    mpz_t tmp;
    mpz_init(tmp);

    if (input < 0)
    {
        mpz_sub_ui(tmp, pubKey->n, -input);
    }
    else
    {
        mpz_set_ui(tmp, input);
    }

    mpz_mul(output, pubKey->n, tmp);
    mpz_add_ui(output, output, 1);

    mpz_mod(output, output, pubKey->nSquared);//the first step of decryption is % n^2 anyway...

    mpz_clear(tmp);
}


void gene_encrypt_rand_data(mpz_t input , mpz_t output, struct PubKey *pubKey)
{

    mpz_mul(output, pubKey->n, input);
    mpz_add_ui(output, output, 1);
    mpz_mod(output, output, pubKey->nSquared);//the first step of decryption is % n^2 anyway...
}

void verify_encrypt_data(mpz_t input , mpz_t bench, struct PubKey *pubKey)
{
    mpz_t result;
    mpz_init(result);
    mpz_mul(result, pubKey->n, input);
    mpz_add_ui(result, result, 1);
    mpz_mod(result, result, pubKey->nSquared);//the first step of decryption is % n^2 anyway...
    assert(0 == mpz_cmp(result, bench));
}

void gene_add_rand_data(mpz_t a, mpz_t b, mpz_t result, struct PubKey *pubKey){
    
    // mpz_init(result);
    mpz_mul(result, a, b);
    mpz_mod(result, result, pubKey->nSquared);
}

void verify_add_data(mpz_t a, mpz_t b, mpz_t bench, struct PubKey *pubKey){
    mpz_t result;
    mpz_init(result);
    mpz_mul(result, a, b);
    mpz_mod(result, result, pubKey->nSquared);
    assert(0 == mpz_cmp(result, bench));
}

void gene_mul_rand_data(mpz_t a, mpz_t b, mpz_t result, struct PubKey *pubKey){
    
    mpz_init(result);
    mpz_powm(result, a, b, pubKey->nSquared);
}

void verify_mul_data(mpz_t a, mpz_t b, mpz_t bench, struct PubKey *pubKey){
    
    mpz_t result;
    mpz_init(result);
    mpz_powm(result, a, b, pubKey->nSquared);
    assert(0 == mpz_cmp(result, bench));
}

void decrypt(mpz_t output, mpz_t input, struct PrivKey *privKey)
{
    mpz_t mp, mq, tmp, tmp2;
    mpz_init(mp);
    mpz_init(mq);
    mpz_init(tmp);
    mpz_init(tmp2);

    // c ^ (p-1) % p^2

    // mp = L(c ^ (p-1) % p^2) * hp % p
    mpz_powm(tmp, input, privKey->pMinusOne, privKey->pSquared);
    // L(c ^ (p-1) % p^2)
    L(tmp, tmp, privKey->p);
    // L(c ^ (p-1) % p^2) * hp
    mpz_mul(tmp, tmp, privKey->hp);
    // mp = L(c ^ (p-1) % p^2) * hp % p
    mpz_mod(mp, tmp, privKey->p);

    mpz_powm(tmp, input, privKey->qMinusOne, privKey->qSquared);
    L(tmp, tmp, privKey->q);

     // tmp = L(c ^ (q-1) % q^2) * hq
    mpz_mul(tmp, tmp, privKey->hq);
    // mp = L(c ^ (q-1) % q^2) * hq % q
    mpz_mod(mq, tmp, privKey->q);

    // tmp  = mp * q^(-1)modp
    mpz_mul(tmp, mp, privKey->qTimesQInvModP);
    // tmp2 = mq * p^(-1)modq
    mpz_mul(tmp2, mq, privKey->pTimesPInvModQ);

    mpz_add(tmp, tmp, tmp2);

    mpz_mod(output, tmp, privKey->n);

    if (mpz_cmp(output, privKey->posNegBoundary) > 0)
    {
        mpz_sub(output, output, privKey->n);
    }

    mpz_clear(mp);
    mpz_clear(mq);
    mpz_clear(tmp);
    mpz_clear(tmp2);
}


void verify_decrypt( mpz_t input, mpz_t bench, struct PrivKey *privKey)
{
    mpz_t output;
    mpz_init(output);

    mpz_t mp, mq, tmp, tmp2;
    mpz_init(mp);
    mpz_init(mq);
    mpz_init(tmp);
    mpz_init(tmp2);

    // c ^ (p-1) % p^2

    // mp = L(c ^ (p-1) % p^2) * hp % p
    mpz_powm(tmp, input, privKey->pMinusOne, privKey->pSquared);
    // L(c ^ (p-1) % p^2)
    L(tmp, tmp, privKey->p);
    // L(c ^ (p-1) % p^2) * hp
    mpz_mul(tmp, tmp, privKey->hp);
    // mp = L(c ^ (p-1) % p^2) * hp % p
    mpz_mod(mp, tmp, privKey->p);

    mpz_powm(tmp, input, privKey->qMinusOne, privKey->qSquared);
    L(tmp, tmp, privKey->q);

     // tmp = L(c ^ (q-1) % q^2) * hq
    mpz_mul(tmp, tmp, privKey->hq);
    // mp = L(c ^ (q-1) % q^2) * hq % q
    mpz_mod(mq, tmp, privKey->q);

    // tmp  = mp * q^(-1)modp
    mpz_mul(tmp, mp, privKey->qTimesQInvModP);
    // tmp2 = mq * p^(-1)modq
    mpz_mul(tmp2, mq, privKey->pTimesPInvModQ);

    mpz_add(tmp, tmp, tmp2);

    mpz_mod(output, tmp, privKey->n);

    if (mpz_cmp(output, privKey->posNegBoundary) > 0)
    {
        mpz_sub(output, output, privKey->n);
    }
    assert(0 == mpz_cmp(output, bench));
    mpz_clear(mp);
    mpz_clear(mq);
    mpz_clear(tmp);
    mpz_clear(tmp2);
}


void paillier_sub(mpz_t a, mpz_t b, mpz_t *result, struct PubKey *pubKey){
    
    mpz_t tmp;
    // mpz_t encSub;
    mpz_init(tmp);
    mpz_init(*result);
    mpz_invert(tmp, b, pubKey->nSquared);
    mpz_mul(*result, a, tmp);
    // return encSub;
}

void paillier_add(mpz_t a, mpz_t b, mpz_t *result, struct PubKey *pubKey){
    
    mpz_t tmp;
    // mpz_t encAdd;
    mpz_init(tmp);
    mpz_init(*result);
    mpz_mul(*result, a, b);
    // return encAdd;
}

void paillier_mul(mpz_t a, long b, mpz_t *result, struct PubKey *pubKey){
    
    mpz_t tmp;
    mpz_t z;
    // mpz_t encAdd;
    mpz_init(tmp);
    mpz_init(z);
    mpz_set_si(z, b);
    mpz_init(*result);
    mpz_powm(*result, a, z, pubKey->nSquared);
    // return encAdd;
}

string serialize_sk(struct PrivKey &sk){

    mpz_t* sk_mpz[] = {&sk.p, &sk.q, &sk.pMinusOne, &sk.qMinusOne, 
                        &sk.hp, &sk.hq, &sk.n,
                        &sk.pSquared, &sk.qSquared,&sk.qTimesQInvModP,
                        &sk.pTimesPInvModQ, &sk.posNegBoundary};

    const int elem_nums = sizeof(sk_mpz) / sizeof(sk_mpz[0]);
    int sk_body_byte_size = 0;
    std::vector<int>sk_each_elem_byte_size(elem_nums);

    for (int i = 0; i < elem_nums; ++i) {
        mpz_t& sk_each_elem = *sk_mpz[i];
        sk_each_elem_byte_size[i] = mpz_size(sk_each_elem)*8;
        sk_body_byte_size += sk_each_elem_byte_size[i];
    }

    char* sk_body_buf = (char*)malloc(sizeof(int)+sk_body_byte_size*sizeof(char));
    int half_n_length = sk_each_elem_byte_size[0];
    std::memcpy(sk_body_buf, reinterpret_cast<char*>(&half_n_length), sizeof(int));

    char* buf = sk_body_buf + sizeof(int);
    for (int i = 0; i < elem_nums; ++i) {
        mpz_export(buf, NULL, 1, 1, 0, 0, *sk_mpz[i]);
        buf += sk_each_elem_byte_size[i];
    }
    
    return string(sk_body_buf,sizeof(int)+sk_body_byte_size*sizeof(char));
}

string serialize_pk(struct PubKey &pk)
{

    mpz_t* pk_mpz[] = {&pk.n, &pk.g, &pk.nSquared};
    const int elem_nums = sizeof(pk_mpz) / sizeof(pk_mpz[0]);
    
    int pk_body_byte_size = 0;
    std::vector<int>pk_each_elem_byte_size(elem_nums);
    for (int i = 0; i < elem_nums; ++i) {
        mpz_t& pk_each_elem = *pk_mpz[i];
        pk_each_elem_byte_size[i] = mpz_size(pk_each_elem) * 8;
        pk_body_byte_size += pk_each_elem_byte_size[i];

    }

    char* pk_body_buf = (char*)malloc(sizeof(int)+pk_body_byte_size*sizeof(char));
    int n_length = pk_each_elem_byte_size[0];
    std::memcpy(pk_body_buf, reinterpret_cast<char*>(&n_length), sizeof(int));

    char* buf = pk_body_buf + sizeof(int);
    for (int i = 0; i < elem_nums; ++i) {
        mpz_export(buf, NULL, 1, 1, 0, 0, *pk_mpz[i]);
        buf += pk_each_elem_byte_size[i];
    }

    return string(pk_body_buf,sizeof(int)+pk_body_byte_size*sizeof(char)); 
}

struct PubKey dserialize_pk(const string& pk_str)
{
    // std::string dd;

    int pk_header_int;
    std::memcpy(&pk_header_int, pk_str.data(), sizeof(int));

    const char* pk_body_buf =  pk_str.c_str()+sizeof(int);
    struct PubKey pubKey;
    mpz_init(pubKey.n);
    mpz_init(pubKey.nSquared);
    mpz_init(pubKey.g);
    
    mpz_import(pubKey.g, pk_header_int, 1, sizeof(char), 0, 0, pk_body_buf);
    mpz_import(pubKey.n, pk_header_int, 1, sizeof(char), 0, 0, pk_body_buf+pk_header_int);
    mpz_import(pubKey.nSquared, 2*pk_header_int, 1, sizeof(char), 0, 0, pk_body_buf+2*pk_header_int);
    return pubKey;

}

struct PrivKey dserialize_sk(string& sk_str){
    
    int sk_half_n_length;
    std::memcpy(&sk_half_n_length, sk_str.data(), sizeof(int));

    struct PrivKey sk;
    initPrivKey(&sk);

    mpz_t* sk_mpz[] = {&sk.p, &sk.q, &sk.pMinusOne, &sk.qMinusOne, 
                        &sk.hp, &sk.hq, &sk.n,
                        &sk.pSquared, &sk.qSquared,&sk.qTimesQInvModP,
                        &sk.pTimesPInvModQ, &sk.posNegBoundary};
    const int num_elems = sizeof(sk_mpz) / sizeof(sk_mpz[0]);
    char* sk_head = &sk_str[0];
    char* sk_buf = sk_head+sizeof(int);
    for(int i = 0; i < SK_L_SIZE; ++i){
        mpz_import(*sk_mpz[i], sk_half_n_length, 1, sizeof(char), 0, 0, sk_buf);
        sk_buf += sk_half_n_length;
    }
    for(int j = SK_L_SIZE; j < SK_L_SIZE+SK_H_SIZE; ++j){
        mpz_import(*sk_mpz[j], sk_half_n_length*2, 1, sizeof(char), 0, 0, sk_buf);
        sk_buf += sk_half_n_length*2;
    }
    return sk;
}

long gen_random(){
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<long> dist(-10000000, 10000000); // specify range here
    // long r_value  = dist(gen);
    return dist(gen);
}

void gen_random_pq( mpz_t p, mpz_t q, unsigned long n_length){
    
    unsigned long primeLen = n_length / 2;
    mpz_t n;
    mpz_init(n);
    do
    {
        getRandomPrime(p, primeLen);
        getRandomPrime(q, primeLen);
        while (!mpz_cmp(p, q))
        {
            getRandomPrime(p, primeLen);
        }
        mpz_mul(n,  p,  q);
    }
    while (mpz_sizeinbase(n, 2) != n_length);
}

struct PubKey init_pk_by_pq(mpz_t p, mpz_t q){
    
    struct PubKey pubKey;
    initPubKey(&pubKey);
    mpz_mul(pubKey.n, p, q);
    mpz_mul(pubKey.nSquared, pubKey.n, pubKey.n);
    mpz_add_ui(pubKey.g, pubKey.n, 1);
    return pubKey;
}

struct PrivKey init_sk_by_pq(mpz_t p, mpz_t q){
    
    struct PrivKey privKey;
    initPrivKey(&privKey);
    mpz_mul(privKey.n, p, q);
    mpz_set(privKey.p, p);
    mpz_set(privKey.q, q);
    mpz_t tmp;
    mpz_init(tmp);
    mpz_t g;
    mpz_init(g);
    mpz_add_ui(g, privKey.n, 1);

    mpz_sub_ui(privKey.pMinusOne, p, 1);
    mpz_sub_ui(privKey.qMinusOne, q, 1);

    mpz_mul(privKey.pSquared, p, p);
    mpz_mul(privKey.qSquared, q, q);

    //compute hp
    mpz_powm(tmp, g, privKey.pMinusOne, privKey.pSquared);
    L(privKey.hp, tmp, privKey.p);
    mpz_invert(privKey.hp, privKey.hp, privKey.p);

    //compute hq
    mpz_powm(tmp, g, privKey.qMinusOne, privKey.qSquared);
    L(privKey.hq, tmp, privKey.q);
    mpz_invert(privKey.hq, privKey.hq, privKey.q);

    mpz_invert(tmp, privKey.p, privKey.q);
    mpz_mul(privKey.pTimesPInvModQ, privKey.p, tmp);
    mpz_invert(tmp, privKey.q, privKey.p);
    mpz_mul(privKey.qTimesQInvModP, privKey.q, tmp);

    mpz_tdiv_q_ui(privKey.posNegBoundary, privKey.n, 2);

    mpz_clear(tmp);
    mpz_clear(g);
    return privKey;
}

void test_encrypt_by_pq(){

}

void test_dencrypt_by_pq(){}

/*
    p 和 q产生测试数据，
    1 带加密数据 m
    2 输入的p和q和n
    3 输出的加密密文
    
    mpz_t x;
    mpz_init(x);

    gmp_randstate_t state;
    gmp_randinit_default(state);

    mpz_urandomb(x, state, 1024);

    gmp_printf("x = %Zd\n", x);

    mpz_clear(x);
    gmp_randclear(state);
*/
void gen_test_data(int data_num, unsigned long n_length, vector<std::string> file_name_list){

    mpz_t p;
    mpz_t q;
    mpz_init(p);
    mpz_init(q);
    struct PubKey pk;
    struct PrivKey sk;
    mpz_t tmp_test;
    mpz_init(tmp_test);

    mpz_t m_mul_res, m_add_res;
    mpz_t m_lhs, m_rhs,m_lhs_cipher, m_rhs_cipher, 
        m_add_cipher, m_mul_cipher, m_add_plain, m_mul_plain;

    mpz_init(m_lhs);
    mpz_init(m_rhs);
    mpz_init(m_lhs_cipher);
    mpz_init(m_rhs_cipher);
    mpz_init(m_add_cipher);
    mpz_init(m_mul_cipher);
    mpz_init(m_add_res);
    mpz_init(m_mul_res);
    mpz_init(m_add_plain);
    mpz_init(m_mul_plain);

    // gmp_randinit_default(state);
    vector<std::ofstream> open_file_list(file_name_list.size());
    for(int i = 0; i < file_name_list.size(); ++i){
        open_file_list[i] = std::ofstream(file_name_list[i]);
    }

    for(int i = 0; i < data_num; ++i){

        gen_random_pq(p, q, n_length);
        pk = init_pk_by_pq(p, q);
        sk = init_sk_by_pq(p, q);

        mpz_urandomb(m_rhs, randomGeneratorState, 1020);
        mpz_urandomb(m_lhs, randomGeneratorState, 1020);

        gene_encrypt_rand_data(m_lhs, m_lhs_cipher, &pk);
        gene_encrypt_rand_data(m_rhs, m_rhs_cipher, &pk);
        gene_add_rand_data(m_lhs_cipher, m_rhs_cipher, m_add_cipher, &pk);
        gene_mul_rand_data(m_lhs_cipher, m_rhs, m_mul_cipher, &pk);
        mpz_mul(m_mul_res, m_lhs, m_rhs);
        mpz_add(m_add_res, m_lhs, m_rhs);
        
        decrypt(m_add_plain, m_add_cipher, &sk);
        decrypt(m_mul_plain, m_mul_cipher, &sk);

        assert(0 == mpz_cmp(m_add_plain, m_add_res));
        assert(0 == mpz_cmp(m_mul_plain, m_mul_res));
       
        open_file_list[0] <<  mpz_get_str(nullptr, 16, p) << std::endl;
        open_file_list[1] <<  mpz_get_str(nullptr, 16, q) << std::endl;
        open_file_list[2] <<  mpz_get_str(nullptr, 16, m_lhs) << std::endl;
        open_file_list[3] <<  mpz_get_str(nullptr, 16, m_rhs) << std::endl;
        open_file_list[4] <<  mpz_get_str(nullptr, 16, m_lhs_cipher) << std::endl;
        open_file_list[5] <<  mpz_get_str(nullptr, 16, m_rhs_cipher) << std::endl;
        open_file_list[6] <<  mpz_get_str(nullptr, 16, m_add_cipher) << std::endl;
        open_file_list[7] <<  mpz_get_str(nullptr, 16, m_mul_cipher) << std::endl;
        open_file_list[8] <<  mpz_get_str(nullptr, 16, m_add_plain) << std::endl;
        open_file_list[9] <<  mpz_get_str(nullptr, 16, m_mul_plain) << std::endl;

    }

    mpz_clear(p);
    mpz_clear(q);
    mpz_clear(m_rhs);
    mpz_clear(m_lhs);
    mpz_clear(m_lhs_cipher);
    mpz_clear(m_rhs_cipher);
    mpz_clear(m_add_cipher);
    mpz_clear(m_mul_cipher);
    mpz_clear(m_add_plain);
    mpz_clear(m_mul_plain);
}

void verify_test_data(vector<std::string> file_name_list){
    
    vector<std::ifstream> open_file_list(file_name_list.size());
    for(int i = 0; i < file_name_list.size(); ++i){
        open_file_list[i] = std::ifstream(file_name_list[i]);
        if (!open_file_list[i].is_open()) {
            std::cerr << "无法打开文件" << std::endl;
            return ;
        }
    }

    mpz_t p, q, m_lhs, m_rhs, m_lhs_cipher, m_rhs_cipher,
          m_add_cipher, m_mul_cipher, m_add_bench, m_mul_bench;
    
    mpz_init(p);
    mpz_init(q);
    mpz_init(m_lhs);
    mpz_init(m_rhs);
    mpz_init(m_lhs_cipher);
    mpz_init(m_rhs_cipher);
    mpz_init(m_add_cipher);
    mpz_init(m_mul_cipher);
    mpz_init(m_add_bench);
    mpz_init(m_mul_bench);

    std::string readline;
    while(std::getline(open_file_list[0], readline)){

            mpz_set_str(p, readline.c_str(), 16);
            std::getline(open_file_list[1], readline);
            mpz_set_str(q, readline.c_str(), 16);
            std::getline(open_file_list[2], readline);
            mpz_set_str(m_lhs, readline.c_str(), 16);
            std::getline(open_file_list[3], readline);
            mpz_set_str(m_rhs, readline.c_str(), 16);
            std::getline(open_file_list[4], readline);
            mpz_set_str(m_lhs_cipher, readline.c_str(), 16);
            std::getline(open_file_list[5], readline);
            mpz_set_str(m_rhs_cipher, readline.c_str(), 16);
            std::getline(open_file_list[6], readline);
            mpz_set_str(m_add_cipher, readline.c_str(), 16);
            std::getline(open_file_list[7], readline);
            mpz_set_str(m_mul_cipher, readline.c_str(), 16);
            std::getline(open_file_list[8], readline);
            mpz_set_str(m_add_bench, readline.c_str(), 16);
            std::getline(open_file_list[9], readline);
            mpz_set_str(m_mul_bench, readline.c_str(), 16);

            struct PubKey pk = init_pk_by_pq(p, q);
            struct PrivKey sk = init_sk_by_pq(p, q);
            //验证两个加密
            verify_encrypt_data(m_lhs, m_lhs_cipher, &pk);
            verify_encrypt_data(m_rhs, m_rhs_cipher, &pk);
            //验证密文计算
            verify_add_data(m_lhs_cipher, m_rhs_cipher, m_add_cipher, &pk);
            verify_mul_data(m_lhs_cipher, m_rhs, m_mul_cipher, &pk);
            verify_decrypt(m_add_cipher,m_add_bench,&sk);
            verify_decrypt(m_mul_cipher,m_mul_bench,&sk);
    }
    mpz_clear(p);
    mpz_clear(q);
    mpz_clear(m_rhs);
    mpz_clear(m_lhs);
    mpz_clear(m_lhs_cipher);
    mpz_clear(m_rhs_cipher);
    mpz_clear(m_add_cipher);
    mpz_clear(m_mul_cipher);
    mpz_clear(m_add_bench);
    mpz_clear(m_mul_bench);
}

void rand_gene(){


    mpz_t rand_num;
    mpz_init(rand_num);

    // Generate a random number between 0 and 9999
    mpz_urandomb(rand_num, randomGeneratorState, 1111);

    gmp_printf("Random number: %Zd\n", rand_num);

    // Clean up resources
    mpz_clear(rand_num);
}


int main(int argc, char *argv[])
{
    randomSeed = getRandomSeed();
    gmp_randinit_default(randomGeneratorState);
    gmp_randseed_ui(randomGeneratorState, randomSeed);

    int data_num = 1000;
    unsigned long n_length = 2048;
    vector<string> file_name_list{"mpz_lhs.txt", "mpz_rhs.txt",
                                 "mpz_add_bench.txt", "mpz_mul_bench.txt",
                                 "mpz_p.txt", "mpz_q.txt", "mpz_lhs_cipher.txt",
                                 "mpz_rhs_cipher.txt", 
                                 "mpz_add_cipher.txt", "mpz_mul_cipher.txt"};
    gen_test_data(data_num,n_length,file_name_list);
    verify_test_data(file_name_list);
    gmp_randclear(randomGeneratorState);
}
