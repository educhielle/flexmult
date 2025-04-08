// MoMA, NYUAD 2023

#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
#include <sstream>
#include <cstdint>
#include <iomanip>
#include <tuple>

using std::string;
using std::cout;

template<class T> struct ivec : std::vector<T>
{
    using Base = std::vector<T>;
    int size() const { return (int)Base::size(); }
    void operator+=(const T & b) { Base::push_back(b); }
    ivec operator+(const T & b) { auto r(*this); r += b; return r; }
    void operator+=(const ivec<T> & x) { Base::insert(Base::end(), x.begin(), x.end()); }
    ivec operator+(const ivec<T> & x) { auto r(*this); r += x; return r; }
    void erase(int i) { Base::erase(Base::begin() + i); }
    void reverse() { std::reverse(Base::begin(), Base::end()); }
    T add(const T & sep) const { T r {}; for ( const T & x : *this) { r += sep; r += x;} return r; }
    string str(const string & sep) const { string r; for ( const T & x : *this) { r += sep; r += std::to_string(x);} return r; }

    ivec(int sz, const T & v = T()) : Base(sz, v) {}
    ivec() : Base() {}
};

#ifndef for_i
#define for_i(x) for(int i=0; i<(x); ++i)
#define for_ir(x) for(int i=(x); i>=0; --i)
#define for_(i,x) for(int i=0; i<(x); ++i)
#endif

#ifndef never
#define nevers(x) (throw std::string("err at ")+(__FILE__)+":"+std::to_string(__LINE__) + " ["+x+"]")
#define never (throw std::string("err at ")+(__FILE__)+":"+std::to_string(__LINE__) + " ["+(__func__)+"]")
#endif


const bool D = !!true;


using reg = uint64_t;
using bit = int;
constexpr int typ_sz = 8 * sizeof(reg);
constexpr int reg_sz = typ_sz * 0 + 16;
constexpr int ops_buf = 2; // must be >=2
int ops_sz;
constexpr int mod_buf = 2; // must be >=2
int mod_sz;
constexpr int rxb = 1;
int nblk;

reg reg_ff = ( ~reg(0) >> (typ_sz - reg_sz) );
int blk_sz;
reg ops_ff = 0;
reg mod_ff = 0;
reg blk_ff = 0;

using vbit = ivec<bit>;

std::ostream & operator<<(std::ostream & os, vbit v)
{
    os << "[";
    for (auto i = v.size(); i != 0; i--)
    {
        auto x = (v[i - 1] & 1);
        os << (x ? 1 : 0);
    }
    os << "]";
    return os;
}

template <class T> inline reg rg(T x) { return reg(x & reg_ff); }

inline bit msb(reg x) { return bit( rg(x) >> (reg_sz - 1) ); }
bit bmsb(reg x);
vbit vmsb(reg x);

vbit vlsb(reg x);
bit blsb(reg x);

std::tuple<bit, bit> bCSA_bit(bit a, bit b, bit c);
std::tuple<vbit, vbit> vCSA_bit(vbit a, vbit b, vbit c);
std::tuple<reg, reg> bCSA_reg(reg a, reg b, reg c);
std::tuple<reg, reg> vCSA_reg(reg a, reg b, reg c);
reg bAND_reg_bit(reg a, bit b);
reg vAND_reg_bit(reg a, vbit b);

reg mont_init_m4(reg mod);
template <int rxb> reg montp(reg m4, reg mod, reg a, reg b, int ctrl_bits);
template <int rxb> reg montp_cores(reg m4, reg mod, reg a, reg b, int ctrl_bits);


inline bit XOR(bit a, bit b) { return a ^ b; }
inline bit AND(bit a, bit b) { return a & b; }
inline bit OR(bit a, bit b) { return a | b; }

vbit vOP(vbit a , vbit b, decltype(XOR) f)
{
    vbit r;
    int sz = a.size(); if (sz != b.size()) never;
    for_i(sz) r += f(a[i], b[i]);
    return r;
}

inline vbit vXOR(vbit a, vbit b) { return vOP(a, b, XOR); }
inline vbit vAND(vbit a, vbit b) { return vOP(a, b, AND); }
inline vbit vOR(vbit a, vbit b) { return vOP(a, b, OR); }


void dmain(int nblocks);

void cmain()
{
    dmain(2);
}

reg modmul(reg a, reg b, reg m)
{
    a %= m;
    b %= m;
    if (b == 0) return 0;
    if (b == 1) return a;
    auto y = (a << 1);
    auto q = (b >> 1);
    y = modmul(y, q, m);
    if (b == (q << 1)) return y;
    return (y + a) % m;
}

void dmain(int nblocks)
{
    nblk = nblocks;

    // compute block values
    blk_sz = reg_sz / nblk;
    ops_sz = blk_sz - ops_buf;
    mod_sz = ops_sz - mod_buf;

    blk_ff = reg_ff >> (blk_sz * (nblk - 1));
    ops_ff = blk_ff >> ops_buf;
    mod_ff = ops_ff >> mod_buf;

    reg mod_max = mod_ff;
    int ctrl_bits = 0x1; // full, no-reduce

    //if ( ops_sz % rxb ) nevers("bit radix must be multiple of ops size");

    for_i(2)
    {
        if (i) cout << std::dec;
        else cout << std::hex;
        cout << "reg_sz=" << reg_sz
             << " blk_sz=" << blk_sz
             << " ops_sz=" << ops_sz
             << " mod_sz=" << mod_sz
             << " rxb=" << rxb
             << " ctrl=" << ctrl_bits << '\n';
        cout << " reg_ff=" << reg_ff
             << " blk_ff=" << blk_ff
             << " ops_ff=" << ops_ff
             << " mod_ff=" << mod_ff << '\n';
    }

    auto comp = [](reg mod, reg reduced, reg x) -> bool
    {
        if ( reduced >= mod ) never;
        if ( x > ops_ff ) never; // return true;
        return reduced != (x % mod);
    };

    if (1)
    {
        reg mod = mod_max - 0, a = mod - 1, b = mod - 2;

        auto m4 = mont_init_m4(mod);
        auto rx = montp_cores<rxb>(m4, mod, a, b, ctrl_bits);
        cout << rx << '\n';
        while (rx >= mod) rx -= mod;
        cout << rx << '\n';
        return;
    }

    int step = 50;
    reg mod_inc = 2 * (mod_max / step);
    reg ops_inc = ops_ff / step;
    if (ops_inc == 0) ops_inc = 1;
    if (mod_inc == 0) mod_inc = 2;

    for (reg mod = 1; mod <= mod_max; mod += mod_inc)
    {
        reg m4 = mont_init_m4(mod);
        cout << "mod m4 : " << mod << ' ' << m4 << '\n';
        for ( reg a = 0; a <= ops_ff; a += ops_inc)
        {
            for (reg b = 0; b <= ops_ff; b += ops_inc)
            {
                auto e = modmul(a, b, mod);
                auto chk = [&](reg x) -> bool
                {
                    if ( comp(mod, e, x) )
                    {
                        cout << "m a b : e x : " << mod << ' ' << a << ' '
                        << b << " => " << e << ' ' << x << '\n';
                        cout << "m a b : e x : " << mod << ' ' << (a % mod) << ' '
                        << (b % mod) << " => " << e << ' ' << (x % mod) << '\n';
                        return false;
                    }
                    return true;
                };

                auto r1 = montp_cores<rxb>(m4, mod, a, b, ctrl_bits);
                if ( !chk(r1) ) return;
            }
        }
    }
}

reg mont_init_m4(reg mod)
{
    auto m2 = ops_ff + 1;
    m2 %= mod;
    auto m4 = m2;
    for_i(ops_sz)
    {
        m4 <<= 1;
        m4 %= mod;
    }
    return m4;
}

template <int rxb> void montp_unit_mul(reg M, reg & P, reg & Q, reg Ap, reg Aq, reg B)
{
    nevers("no generic implementation");
}

struct Pr { reg val; };
std::ostream & operator << (std::ostream & os, Pr p)
{
    return os
           << std::hex << std::setw(reg_sz / 4)
           << std::setfill('0') << p.val;
}

template <>
void montp_unit_mul<1>(reg M, reg & P, reg & Q, reg Ap, reg Aq, reg B)
{
    if (D) cout << std::hex;
    if (D) cout << "M Ap Aq B : " << Pr {M} << ' ' << Pr {Ap}
                    << ' ' << Pr {Aq} << ' ' << Pr {B} << '\n';

    using std::tie;

    vbit ai_this(nblk), ai_carry(nblk), ai_next(nblk);

    auto cook_ai = [&]()
    {
        vbit apb = vlsb(Ap);
        vbit aqb = vlsb(Aq);
        tie(ai_next, ai_carry) = vCSA_bit(apb, aqb, ai_carry);
    };

    cook_ai(); // need extra work for later parallel
    ai_this = ai_next;
    for_(idummy, ops_sz)
    {
        // thread 1 - order independent
        {
            Ap >>= 1; Aq >>= 1;
            cook_ai();
        }

        // thread 2
        reg Bai = vAND_reg_bit(B, ai_this);
        tie(P, Q) = vCSA_reg(P, Q, Bai);
        reg Mp = vAND_reg_bit(M, vlsb(P));
        tie(P, Q) = vCSA_reg(P, Q, Mp);
        P >>= 1; Q >>= 1;

        if (D) cout << "(EOC) i P Q Bai ai_this ai_next : "
                        //<< std::dec
                        << idummy << ' '
                        << Pr {P} << ' ' << Pr {Q} << ' ' << Pr {Bai}
                        << ' ' << ai_this << ' ' << ai_next << '\n';

        // use pre-computed bit
        ai_this = ai_next;
    }
}

template <>
void montp_unit_mul<2>(reg M, reg & P, reg & Q, reg Ap, reg Aq, reg B)
{
    nevers("rxb=2 NI");
}

template <int rxb>
reg montp(reg m4, reg m, reg a, reg b, int ctrl_bits)
{

    // ctrl_bits
    // ...x : 1 - full multiplication; 0 - mont mult
    // ..x. : 1 - do final reduction; 0 - no reduct
    bool full_mult = !!(ctrl_bits & 1);
    bool final_reduction = !!(ctrl_bits & 2);

    reg p = 0, q = 0;
    reg ap = reg {}, aq = reg {};

    if ( full_mult )
    {
        montp_unit_mul<rxb>(m, p, q, a, reg(0), m4);
        ap = p;
        aq = q;
        p = q = 0;
    }
    else
    {
        ap = a, aq = 0;
    }

    montp_unit_mul<rxb>(m, p, q, ap, aq, b);
    auto r = p + q;

    if ( final_reduction ) // BEWARE addition in not working with cores
    {
        auto rm = r + (~m) + 1;
        if ( !msb(rm) ) r = rm;
    }

    return r;
}

template <int rxb>
reg montp_cores(reg m4, reg m, reg a0, reg b0, int ctrl_bits)
{
    reg ac = a0, bc = b0, mc = m, fc = m4;

    auto ops_mod = ops_ff + 1;

    auto va = [&](int i) { return i == 0 ? a0 : ((i + a0) % ops_mod); };
    auto vb = [&](int i) { return i == 0 ? b0 : ((i + b0 + 17) % ops_mod); };

    for (int i = 1; i < nblk; i++ )
    {
        ac <<= blk_sz; ac |= va(i);
        bc <<= blk_sz; bc |= vb(i);
        mc <<= blk_sz; mc |= m;
        fc <<= blk_sz; fc |= m4;
    }

    reg rc0 = montp<rxb>(fc, mc, ac, bc, ctrl_bits);
    reg r = rc0 >> ((nblk - 1) * blk_sz);

    auto rc = rc0; // for dbg
    if (D) cout << "rc: " << rc << '\n';
    for (int i = nblk - 1; i >= 0; i--)
    {
        reg gotval = (rc & blk_ff);
        reg a = va(i), b = vb(i);
        reg expval = modmul(a, b, m);
        if ( gotval % m !=  expval % m )
            nevers("Core fault");
        if (D) cout << "exp/got: " << expval << ' ' << gotval << '\n';
        rc >>= blk_sz;
    }
    return r;
}

std::tuple<bit, bit> bCSA_bit(bit a, bit b, bit ci)
{
    auto x = XOR(a, b);
    auto s = XOR(x, ci);
    auto ab = AND(a, b);
    auto y = AND(ci, x);
    auto co = OR(ab, y);
    return {s, co};
}

std::tuple<vbit, vbit> vCSA_bit(vbit a, vbit b, vbit ci)
{
    auto x = vXOR(a, b);
    auto s = vXOR(x, ci);
    auto ab = vAND(a, b);
    auto y = vAND(ci, x);
    auto co = vOR(ab, y);
    return { s, co };
}

struct access_bit
{
        access_bit(reg & a, int i): val(a), index(i) {}
        operator bit() const;
        void operator=(bit b);

    private:
        int index;
        reg & val;
};

inline void access_bit::operator=(bit b)
{
    reg u {1}; u <<= index;
    if (b) val |= u;
    else val &= ~u;
}

inline access_bit::operator bit() const
{
    reg v = (val >> index);
    if ( blsb(v) ) return bit {1};
    return bit {0};
}

reg bAND_reg_bit(reg a, bit b)
{
    reg r = reg {};
    // parallel
    for_i(reg_sz)
    {
        auto ri = access_bit(r, i);
        auto ai = access_bit(a, i);
        ri = AND( bit(ai), b );
    }

    return r;
}

reg vAND_reg_bit(reg a, vbit b)
{
    reg r = reg {};
    // parallel
    for_i(reg_sz)
    {
        auto ri = access_bit(r, i);
        auto ai = access_bit(a, i);
        ri = AND(bit(ai), b[i / blk_sz]); // SW
        // core size **
    }

    return r;
}

std::tuple<reg, reg> bCSA_reg(reg x, reg y, reg z)
{
    reg sr = reg {}, cr = reg {};
    // parallel
    for_i(reg_sz)
    {
        auto si = access_bit(sr, i);
        auto ci = access_bit(cr, i);
        auto xi = access_bit(x, i);
        auto yi = access_bit(y, i);
        auto zi = access_bit(z, i);
        auto [s, c] = bCSA_bit(xi, yi, zi);
        si = s;
        ci = c;
    }

    return {sr, cr << 1};
}

std::tuple<reg, reg> vCSA_reg(reg x, reg y, reg z)
{
    reg sr = reg {}, cr = reg {};
    // parallel
    for_i(reg_sz)
    {
        auto si = access_bit(sr, i);
        auto ci = access_bit(cr, i);
        auto xi = access_bit(x, i);
        auto yi = access_bit(y, i);
        auto zi = access_bit(z, i);
        auto [s, c] = bCSA_bit(xi, yi, zi);
        si = s;
        ci = c;
        if ((i + 1) % blk_sz == 0) ci = bit {}; // SW
        // index of bit is multple of block size , the carry is 0, no propagate to next core
    }

    return { sr, cr << 1 };
}

vbit vlsb(reg x)
{
    vbit r;
    for_i(nblk)
    {
        r += bit(rg(x)) & bit { 1 };
        x >>= blk_sz;
    }
    return r;
}

bit blsb(reg x) { return bit(rg(x)) & bit { 1 }; }

std::vector<string> args;
string arg0;
void cmain();
int main(int ac, const char * av[])
try
{
    for ( int i = 1; i < ac; i++ ) args.push_back(av[i]);
    arg0 = av[0];
    cmain();
}

catch (int e)
{
    cout << "error (int): " << e << "\n";
    return 1;
}
catch (string e)
{
    cout << "error: " << e << "\n";
    return 1;
}
catch (const char * e)
{
    cout << "error: " << e << "\n";
    return 1;
}
catch (std::exception & e)
{
    cout << "error (std): " << e.what() << "\n";
    return 1;
}
catch (...)
{
    cout << "Unknown exception\n";
    return 1;
}
