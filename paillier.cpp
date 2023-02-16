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
    mpz_t nSquared;
    mpz_t g;
};

#define SK_L_SIZE 6
#define SK_H_SIZE 5
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
    mpz_t pSquared;
    mpz_t qSquared;
    mpz_t qTimesQInvModP;
    mpz_t pTimesPInvModQ;
    mpz_t posNegBoundary;
};

void initPubKey(struct PubKey *pubKey)
{
    mpz_init(pubKey->n);
    mpz_init(pubKey->nSquared);
    mpz_init(pubKey->g);
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
    mpz_clear(privKey->pSquared);
    mpz_clear(privKey->qSquared);
    mpz_clear(privKey->hp);
    mpz_clear(privKey->hq);
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

    // printf("n: ");
    // print(pubKey->n);
    // printf("Positive / negative boundary: ");
    // print(privKey->posNegBoundary);
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

    //mpz_mod(output, output, pubKey->nSquared);//the first step of decryption is % n^2 anyway...

    mpz_clear(tmp);
}

void decrypt1(mpz_t output, mpz_t input, struct PubKey *pubKey, struct PrivKey *privKey)
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
    
    // u = mul_mod((mq - mp), self.p_inverse, self.q)
    // mp + (u * self.p)
    // tmp = mp * q^(-1)modp + mp * q^(-1)modp
    mpz_t sub_tmp, tmp123;
    mpz_init(sub_tmp);
    mpz_init(tmp123);
    if (mpz_cmp(mq, mp) > 0)
    {
        mpz_sub(sub_tmp, mq, mp);
        mpz_mul(tmp123, sub_tmp, privKey->pTimesPInvModQ);
        mpz_mod(tmp123, tmp123, privKey->q);
        mpz_add(tmp, tmp123, mp);
        
    }else{
        mpz_sub(sub_tmp, mp, mq);
        mpz_mul(tmp123, sub_tmp, privKey->qTimesQInvModP);
        mpz_mod(tmp123, tmp123, privKey->p);
        mpz_add(tmp, tmp123, mq);
    }

    mpz_mod(output, tmp, pubKey->n);

    if (mpz_cmp(output, privKey->posNegBoundary) > 0)
    {
        mpz_sub(output, output, pubKey->n);
    }

    mpz_clear(mp);
    mpz_clear(mq);
    mpz_clear(tmp);
    mpz_clear(tmp2);
}


void decrypt2(mpz_t output, mpz_t input, struct PubKey *pubKey, struct PrivKey *privKey)
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

    mpz_mod(output, tmp, pubKey->n);

    if (mpz_cmp(output, privKey->posNegBoundary) > 0)
    {
        mpz_sub(output, output, pubKey->n);
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
    // mpz_t encAdd;
    mpz_init(tmp);
    mpz_init(*result);
    mpz_mul(*result, a, b);
    // return encAdd;
}

void testHomomorphicSubtraction(long lhs, long rhs, struct PubKey *pubKey, struct PrivKey *privKey)
{
    //encryptions
    mpz_t encLhs, encRhs;
    mpz_init(encLhs);
    mpz_init(encRhs);

    //descryptions
    mpz_t decLhs, decRhs;
    mpz_init(decLhs);
    mpz_init(decRhs);

    //homomorphic operation result
    mpz_t encSub, decSub;
    mpz_init(encSub);
    mpz_init(decSub);

    mpz_t tmp;
    mpz_init(tmp);

    //encrypt
    encrypt_ul(encLhs, lhs, pubKey);
    encrypt_ul(encRhs, rhs, pubKey);


    //decrypt
    clock_t start = clock();
    // 在此处放置要测试的代码
    for(int i = 0; i < 1; ++i){
        decrypt2(decLhs, encLhs, pubKey, privKey);
    }

    clock_t end = clock();
    double duration = (double)(end - start) / CLOCKS_PER_SEC;
    printf("decrypt1 use time is %f \n",duration);
    
    clock_t start1 = clock();
    for(int i = 0; i < 1; ++i){
        decrypt2(decRhs, encRhs, pubKey, privKey);
    }
    clock_t end1 = clock();
    double duration1 = (double)(end1 - start1) / CLOCKS_PER_SEC;
    printf("decrypt2 use time is %f \n",duration1);

    printf("Decrypted lhs: ");
    print(decLhs);
    printf("Decrypted rhs: ");
    print(decRhs);

    //homomorphic subtraction
    mpz_invert(tmp, encRhs, pubKey->nSquared);
    mpz_mul(encSub, encLhs, tmp);
    //mpz_mod(sub, sub, nSquared);//the first step of decryption is % n^2 anyway...

    decrypt2(decSub, encSub, pubKey, privKey);

    printf("Decrypted subtraction: ");
    print(decSub);

    mpz_clear(encLhs);
    mpz_clear(encRhs);
    mpz_clear(decLhs);
    mpz_clear(decRhs);
    mpz_clear(encSub);
    mpz_clear(decSub);

    mpz_clear(tmp);
}

string serialize_SK(struct PrivKey &sk){

    mpz_t* sk_mpz[] = {&sk.p, &sk.q, &sk.pMinusOne, &sk.qMinusOne, 
                        &sk.hp, &sk.hq, &sk.qTimesQInvModP, 
                        &sk.pSquared, &sk.qSquared,
                        &sk.pTimesPInvModQ, &sk.posNegBoundary};
    const int num_elems = sizeof(sk_mpz) / sizeof(sk_mpz[0]);
    
    int sk_body_byte_size = 0;
    std::vector<int>sk_each_elem_byte_size(num_elems);
    for (int i = 0; i < num_elems; ++i) {
        mpz_t& sk_each_elem = *sk_mpz[i];
        sk_each_elem_byte_size[i] = mpz_size(sk_each_elem)*8;
        sk_body_byte_size += sk_each_elem_byte_size[i];
        // printf("elem in %d has byte size is %d \n",i,sk_each_elem_byte_size[i]);
    }
    printf("sk_body_byte_size is %d \n",sk_body_byte_size);
    char* sk_body_buf = (char*)malloc(sizeof(int)+sk_body_byte_size*sizeof(char));
    int half_n_length = sk_each_elem_byte_size[0];
    std::memcpy(sk_body_buf, reinterpret_cast<char*>(&half_n_length), sizeof(int));

    char* buf = sk_body_buf + sizeof(int);
    for (int i = 0; i < num_elems; ++i) {
        mpz_export(buf, NULL, 1, 1, 0, 0, *sk_mpz[i]);
        buf += sk_each_elem_byte_size[i];
    }
    
    printf("half_n_length = %d \n",half_n_length);
    return string(sk_body_buf,sizeof(int)+sk_body_byte_size*sizeof(char));
}

struct PrivKey dserialize_SK(string& sk_str){
    int sk_half_n_length;
    std::memcpy(&sk_half_n_length, sk_str.data(), sizeof(int));

    printf("read sk_half_n_length = %d \n",sk_half_n_length);
    struct PrivKey sk;
    initPrivKey(&sk);

    mpz_t* sk_mpz[] = {&sk.p, &sk.q, &sk.pMinusOne, &sk.qMinusOne, 
                        &sk.hp, &sk.hq, &sk.qTimesQInvModP, 
                        &sk.pSquared, &sk.qSquared,
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

string serialize_PK(const struct PubKey &pk, struct PubKey *pk1)
{
    // std::string dd;

    int n_length = mpz_size(pk.n)*8;
    printf("n_length = %d \n",n_length);
    char n_length_bytes[sizeof(int)];
    std::memcpy(n_length_bytes, reinterpret_cast<char*>(&n_length), sizeof(int));

    std::string n_header_str(n_length_bytes, sizeof(int));
    // serialized_str.append(data_str);

    size_t pk_size = mpz_size(pk.g); 
    pk_size += mpz_size(pk.n); 
    pk_size += mpz_size(pk.nSquared); 

    char *buf = (char *) malloc(pk_size*8 * sizeof(char));

    mpz_export(buf, NULL, 1, 1, 0, 0, pk.g);
    // buf+=256;
    mpz_export(buf+n_length, NULL, 1, 1, 0, 0, pk.n);
    // buf+=256;
    mpz_export(buf+2*n_length, NULL, 1, 1, 0, 0, pk.nSquared);
       
    mpz_import(pk1->g, n_length, 1, sizeof(char), 0, 0, buf);
    mpz_import(pk1->n, n_length, 1, sizeof(char), 0, 0, buf+n_length);
    mpz_import(pk1->nSquared, 2*n_length, 1, sizeof(char), 0, 0, buf+2*n_length);
    // return pubKey;
    std::string pk_body_str(buf, pk_size*8);

    return  n_header_str.append(pk_body_str);
}

struct PubKey dserialize_PK(const string& pk_str)
{
    // std::string dd;

    int pk_header_int;
    std::memcpy(&pk_header_int, pk_str.data(), sizeof(int));
    // pk_header_int = *reinterpret_cast<int*>(&pk_header_int);
    printf("read pk header = %d \n",pk_header_int);
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

void dserialized_PK(const string& pk_str, struct PubKey *pubKey)
{
    // std::string dd;
    const char* buf =  pk_str.c_str();
    mpz_init(pubKey->n);
    mpz_init(pubKey->nSquared);
    mpz_init(pubKey->g);
    
    mpz_import(pubKey->g, 256, 1, sizeof(char), 0, 0, buf);
    mpz_import(pubKey->n, 256, 1, sizeof(char), 0, 0, buf+256);
    mpz_import(pubKey->nSquared, 512, 1, sizeof(char), 0, 0, buf+512);
    // return pubKey;

}
long gen_random(){
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<long> dist(-100000000, 100000000); // specify range here
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
    string pk_str = serialize_PK(pubKey,&pubKey1);
    string sk_str = serialize_SK(privKey);

    struct  PrivKey skey = dserialize_SK(sk_str);
    struct PubKey pkey = dserialize_PK(pk_str);
    
    // dserialized_PK(pk_str,&pkey);
    long lhs;
    long rhs;
    if(argc > 2){
        lhs = strtol(argv[1], NULL, 10);
        rhs = strtol(argv[2], NULL, 10);
    }else{
        lhs = gen_random();
        rhs = gen_random();
    }


    printf("Testing: %ld - %ld\n", lhs, rhs);
    printf("result: %ld \n", lhs-rhs);
    // testHomomorphicSubtraction(lhs, rhs, &pkey, &skey);
    mpz_t encLhs, encRhs, res, plain_res;
    mpz_init(encLhs);
    mpz_init(encRhs);
    // mpz_init(res);
    mpz_init(plain_res);
    encrypt_ul(encLhs, lhs, &pubKey);
    encrypt_ul(encRhs, rhs, &pubKey);
    paillier_add(encLhs, encRhs, &res, &pubKey);

    decrypt2(plain_res, res, &pubKey, &privKey);
    mpz_t a;
    long b = lhs+rhs;
    mpz_init_set_si(a, b);
    int cmp = mpz_cmp(a, plain_res);
    assert(cmp == 0);
    printf("benchmarch = %ld \n",cmp);
    printf("add result: %ld \n", lhs+rhs);
    print(plain_res);

    freePubKey(&pubKey);
    freePrivKey(&privKey);

    return 0;
}
