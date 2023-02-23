#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <cstring>
#include <gmp.h>
#include <vector>
#include <ctime>
#include <cassert>
#include <random>

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

void paillier_sub(mpz_t a, mpz_t b, mpz_t *result, struct PubKey *pubKey){
    
    mpz_t tmp;
    // mpz_t encSub;
    mpz_init(tmp);
    mpz_init(*result);
    mpz_invert(tmp, b, pubKey->nSquared);
    mpz_mul(*result, a, tmp);
    mpz_mod(*result,*result,pubKey->nSquared);
    // return encSub;
}

void paillier_add(mpz_t a, mpz_t b, mpz_t *result, struct PubKey *pubKey){
    
    mpz_t tmp;
    // mpz_t encAdd;
    mpz_init(tmp);
    mpz_init(*result);
    mpz_mul(*result, a, b);
    mpz_mod(*result,*result,pubKey->nSquared);
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
    std::uniform_int_distribution<long> dist(-pow(2,20)-1, pow(2,20)); // specify range here
    // long r_value  = dist(gen);
    return dist(gen);
}

int main(int argc, char *argv[])
{
    randomSeed = getRandomSeed();
    gmp_randinit_default(randomGeneratorState);
    gmp_randseed_ui(randomGeneratorState, randomSeed);

    struct PubKey pubKey;
    struct PrivKey privKey;
    initPubKey(&pubKey);
    initPrivKey(&privKey);
    generateKeys(&pubKey, &privKey, 2048);

    struct PubKey pubKey1;
    initPubKey(&pubKey1);
    string pk_str = serialize_pk(pubKey);
    string sk_str = serialize_sk(privKey);

    struct  PrivKey skey = dserialize_sk(sk_str);
    struct PubKey pkey = dserialize_pk(pk_str);
    
    long lhs;
    long rhs;

    if(argc == 3){
        lhs = strtol(argv[1], NULL, 10);
        rhs = strtol(argv[2], NULL, 10);
    }else{
        lhs = gen_random();
        rhs = gen_random();
    }

    mpz_t encLhs, encRhs, mul_res, add_res, mul_plain_res, add_plain_res;
    mpz_init(encLhs);
    mpz_init(encRhs);
    mpz_init(mul_plain_res);
    mpz_init(add_plain_res);

    encrypt_ul(encLhs, lhs, &pubKey);
    encrypt_ul(encRhs, rhs, &pubKey);

    paillier_mul(encLhs, rhs, &mul_res, &pubKey);
    paillier_add(encLhs, encRhs, &add_res, &pubKey);

    decrypt(mul_plain_res, mul_res, &privKey);
    decrypt(add_plain_res, add_res, &privKey);

    mpz_t mpz_mul_bench;
    long mul_bench = lhs * rhs;
    mpz_init_set_si(mpz_mul_bench, mul_bench);
    int mul_cmp = mpz_cmp(mpz_mul_bench, mul_plain_res);

    mpz_t mpz_add_bench;
    long add_bench = lhs + rhs;
    mpz_init_set_si(mpz_add_bench, add_bench);
    int add_cmp = mpz_cmp(mpz_add_bench, add_plain_res);

    assert(mul_cmp == 0 && add_cmp==0);
    printf("paillier mul and add get right result \n");

    printf("Testing input: %ld , %ld\n", lhs, rhs);
    // printf("benchmarch = %ld \n",cmp);
    printf("mul bench: %ld \n", mul_bench );
    printf("mul res:  ");
    print(mul_plain_res);

    printf("add bench: %ld \n", add_bench );
    printf("add res:  ");
    print(add_plain_res);

    freePubKey(&pubKey);
    freePrivKey(&privKey);

    return 0;
}
