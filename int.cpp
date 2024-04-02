#include <botan/hex.h>
#include <botan/internal/loadstor.h>
#include <botan/internal/mp_core.h>
#include <botan/internal/stl_util.h>
#include <botan/rng.h>
#include <array>
#include <iostream>

namespace Botan {

template <size_t N>
void dump(const char* s, const std::array<uint64_t, N>& x) {
   printf("%s [%lu] = ", s, N);
   for(size_t i = 0; i != N; ++i) {
      printf("%016lX ", x.at(N - i - 1));
   }
   printf("\n");
}

template <size_t N>
class StringLiteral {
   public:
      constexpr StringLiteral(const char (&str)[N]) { std::copy_n(str, N, value); }

      char value[N];
};

template <WordType W>
inline constexpr auto monty_inverse(W a) -> W {
   if(a % 2 == 0) {
      throw Invalid_Argument("monty_inverse only valid for odd integers");
   }

   /*
   * From "A New Algorithm for Inversion mod p^k" by Çetin Kaya Koç
   * https://eprint.iacr.org/2017/411.pdf sections 5 and 7.
   */

   W b = 1;
   W r = 0;

   for(size_t i = 0; i != WordInfo<word>::bits; ++i) {
      const W bi = b % 2;
      r >>= 1;
      r += bi << (WordInfo<word>::bits - 1);

      b -= a * bi;
      b >>= 1;
   }

   // Now invert in addition space
   r = (WordInfo<word>::max - r) + 1;

   return r;
}

template <WordType W, size_t N, size_t XN>
inline consteval std::array<W, N> reduce_mod(const std::array<W, XN>& x, const std::array<W, N>& p) {
   std::array<W, N + 1> r = {0};
   std::array<W, N + 1> t = {0};

   const size_t x_bits = XN * WordInfo<W>::bits;

   for(size_t i = 0; i != x_bits; ++i) {
      const size_t b = x_bits - 1 - i;

      const size_t b_word = b / WordInfo<W>::bits;
      const size_t b_bit = b % WordInfo<W>::bits;
      const bool x_b = (x[b_word] >> b_bit) & 1;

      shift_left<1>(r);
      if(x_b) {
         r[0] += 1;
      }

      const W carry = bigint_sub3(t.data(), r.data(), N + 1, p.data(), N);

      if(carry == 0) {
         std::swap(r, t);
      }
   }

   std::array<W, N> rs;
   std::copy(r.begin(), r.begin() + N, rs.begin());
   return rs;
}

template <WordType W, size_t N>
inline consteval std::array<W, N> montygomery_r(const std::array<W, N>& p) {
   std::array<W, N + 1> x = {0};
   x[N] = 1;
   return reduce_mod(x, p);
}

template <WordType W, size_t N>
inline consteval std::array<W, N> mul_mod(const std::array<W, N>& x,
                                          const std::array<W, N>& y,
                                          const std::array<W, N>& p) {
   std::array<W, 2 * N> z;
   comba_mul<N>(z.data(), x.data(), y.data());
   return reduce_mod(z, p);
}

template <WordType W, size_t N, size_t ZL>
inline constexpr auto bigint_monty_redc(const std::array<W, ZL>& z, const std::array<W, N>& p, word p_dash)
   -> std::array<W, N> {
   static_assert(N >= 1);
   static_assert(ZL <= 2 * N);

   //std::array<W, N> ws;
   std::vector<W> ws(N);

   W w2 = 0, w1 = 0, w0 = 0;

   w0 = z[0];

   ws[0] = w0 * p_dash;

   word3_muladd(&w2, &w1, &w0, ws[0], p[0]);

   w0 = w1;
   w1 = w2;
   w2 = 0;

   for(size_t i = 1; i != N; ++i) {
      for(size_t j = 0; j < i; ++j) {
         word3_muladd(&w2, &w1, &w0, ws[j], p[i - j]);
      }

      word3_add(&w2, &w1, &w0, i < ZL ? z[i] : 0);

      ws[i] = w0 * p_dash;

      word3_muladd(&w2, &w1, &w0, ws[i], p[0]);

      w0 = w1;
      w1 = w2;
      w2 = 0;
   }

   for(size_t i = 0; i != N - 1; ++i) {
      for(size_t j = i + 1; j != N; ++j) {
         word3_muladd(&w2, &w1, &w0, ws[j], p[N + i - j]);
      }

      word3_add(&w2, &w1, &w0, N + i < ZL ? z[N + i] : 0);

      ws[i] = w0;

      w0 = w1;
      w1 = w2;
      w2 = 0;
   }

   word3_add(&w2, &w1, &w0, (2 * N - 1) < ZL ? z[2 * N - 1] : 0);

   ws[N - 1] = w0;

   std::array<W, N> r = {0};
   for(size_t i = 0; i != std::min(ZL, N); ++i) {
      r[i] = z[i];
   }
   bigint_monty_maybe_sub<N>(r.data(), w1, ws.data(), p.data());

   return r;
}

template <WordType W, size_t N>
inline constexpr std::array<W, N> monty_mul(const std::array<W, N>& x,
                                            const std::array<W, N>& y,
                                            const std::array<W, N>& p,
                                            W p_dash) {
   std::array<W, 2 * N> z;
   comba_mul<N>(z.data(), x.data(), y.data());
   return bigint_monty_redc(z, p, p_dash);
}

template <WordType W, size_t N>
inline constexpr std::array<W, N> monty_sqr(const std::array<W, N>& x, const std::array<W, N>& p, W p_dash) {
   std::array<W, 2 * N> z;
   comba_sqr<N>(z.data(), x.data());
   return bigint_monty_redc(z, p, p_dash);
}

template <WordType W, size_t N>
inline constexpr std::array<W, N> add_mod(const std::array<W, N>& x,
                                          const std::array<W, N>& y,
                                          const std::array<W, N>& p) {
   std::array<W, N> s;
   W carry = bigint_add3_nc(s.data(), x.data(), N, y.data(), N);

   std::array<W, N> r;
   bigint_monty_maybe_sub<N>(r.data(), carry, s.data(), p.data());
   return r;
}

template <uint8_t X, WordType W, size_t N>
inline consteval std::array<W, N> p_minus(const std::array<W, N>& p) {
   static_assert(X > 0);
   std::array<W, N> r;
   W x = X;
   bigint_sub3(r.data(), p.data(), N, &x, 1);
   return r;
}

template <WordType W, size_t N>
inline constexpr uint8_t get_bit(size_t i, const std::array<W, N>& p) {
   const size_t w = i / WordInfo<W>::bits;
   const size_t b = i % WordInfo<W>::bits;

   return static_cast<uint8_t>((p[w] >> b) & 0x01);
}

template <WordType W, size_t N>
inline consteval size_t count_bits(const std::array<W, N>& p) {
   size_t b = WordInfo<W>::bits * N;

   while(get_bit(b - 1, p) == 0) {
      b -= 1;
   }

   return b;
}

template <StringLiteral PS>
class MontgomeryInteger {
   private:
      typedef word W;

      static const constexpr auto P = hex_to_words<W>(PS.value);
      static const constexpr size_t N = P.size();

      // One can dream
      //static_assert(is_prime(P), "Montgomery Modulus must be a prime");
      static_assert(N > 0 && (P[0] & 1) == 1, "Invalid Montgomery modulus");

      static const constexpr W P_dash = monty_inverse(P[0]);

      static const constexpr auto R1 = montygomery_r(P);
      static const constexpr auto R2 = mul_mod(R1, R1, P);
      static const constexpr auto R3 = mul_mod(R1, R2, P);

      static const constexpr auto P_MINUS_2 = p_minus<2>(P);

   public:
      static const constexpr size_t BITS = count_bits(P);
      static const constexpr size_t BYTES = (BITS + 7) / 8;

      typedef MontgomeryInteger<PS> Self;

      MontgomeryInteger(const Self& other) = default;
      MontgomeryInteger(Self&& other) = default;
      MontgomeryInteger& operator=(const Self& other) = default;
      MontgomeryInteger& operator=(Self&& other) = default;

      // ??
      //~MontgomeryInteger() { secure_scrub_memory(m_val); }

      static constexpr Self zero() { return Self(std::array<W, N>{0}); }

      static constexpr Self one() { return Self(Self::R1); }

      constexpr bool is_zero() const { return CT::all_zeros(m_val.data(), m_val.size()).as_bool(); }

      constexpr bool is_one() const { return (*this == Self::one()); }

      // This happens to work without converting from Montgomery form
      constexpr bool is_even() const { return (m_val[0] & 0x01) == 0x00; }

      friend constexpr Self operator+(const Self& a, const Self& b) {
         return Self(add_mod(a.value(), b.value(), Self::P));
      }

      friend constexpr Self operator-(const Self& a, const Self& b) { return a + b.negate(); }

      friend constexpr Self operator*(uint8_t a, const Self& b) {
         return b * a;
      }

      friend constexpr Self operator*(const Self& a, uint8_t b) {
         // We assume b is a small constant and allow variable time
         // computation

         // should we bother with these special cases???
         if(b == 0) {
            return Self::zero();
         } else if(b == 1) {
            return a;
         } else if(b == 2) {
            return a.dbl();
         } else if(b == 3) {
            return a.dbl() + a;
         } else if(b == 4) {
            return a.dbl().dbl();
         } else if(b == 8) {
            return a.dbl().dbl().dbl();
         }

         Self z = Self::zero();
         Self x = a;

         while(b > 0) {
            if(b & 1) {
               z = z + x;
            }
            x = x.dbl();
            b >>= 1;
         }

         return z;
      }

      friend constexpr Self operator*(const Self& a, const Self& b) {
         return Self(monty_mul(a.value(), b.value(), Self::P, Self::P_dash));
      }

      constexpr void conditional_add(bool predicate, const Self& other) { conditional_assign(predicate, *this + other); }

      constexpr void conditional_mul(bool predicate, const Self& other) { conditional_assign(predicate, *this * other); }

      constexpr void conditional_sub(bool predicate, const Self& other) { conditional_add(predicate, other.negate()); }

      constexpr void conditional_assign(bool predicate, const Self& other) {
         CT::conditional_assign_mem(static_cast<W>(predicate), m_val.data(), other.ptr(), N);
      }

      // fixme be faster
      constexpr Self dbl() const { return (*this) + (*this); }

      constexpr Self square() const { return Self(monty_sqr(this->value(), Self::P, Self::P_dash)); }

      // Negation modulo p
      constexpr Self negate() const {
         auto x_is_zero = CT::all_zeros(this->ptr(), N);

         std::array<W, N> r;
         bigint_sub3(r.data(), Self::P.data(), N, this->ptr(), N);
         x_is_zero.if_set_zero_out(r.data(), N);
         return Self(r);
      }

      /**
      * Returns the modular inverse, or 0 if no modular inverse exists.
      *
      * If the modulus is prime the only value that has no modular inverse is 0.
      *
      * This uses Fermat's little theorem, and so assumes that p is prime
      */
      constexpr Self invert() const {
         auto x = (*this);
         auto y = Self::one();

         for(size_t i = 0; i != Self::BITS; ++i) {
            auto b = get_bit(i, P_MINUS_2);
            y.conditional_mul(b, x);
            x = x.square();
         }

         return y;
      }

      constexpr bool operator==(const Self& other) const { return CT::is_equal(this->ptr(), other.ptr(), N).as_bool(); }

      constexpr bool operator!=(const Self& other) const {
         return CT::is_not_equal(this->ptr(), other.ptr(), N).as_bool();
      }

      constexpr std::array<uint8_t, Self::BYTES> serialize() const {
         auto v = bigint_monty_redc(m_val, Self::P, Self::P_dash);
         std::reverse(v.begin(), v.end());
         return store_be(v);
      }

      // TODO:

      /*
      constexpr static Self deserialize(std::array<uint8_t, Self::BYTES> b) {

      }

      static constexpr Self from_wide_bytes(std::array<uint8_t, 2*Self::BYTES> b) {

      }

      static constexpr?? Self from_bigint(const BigInt& bn) {

      }

      static constexpr Self ct_select(std::span<const Self> several, size_t idx) {

      }

      static constexpr Self random(RandomNumberGenerator& rng) {

      }

      */

      template <size_t N>
      static consteval Self constant(StringLiteral<N> S) {
         return Self::constant(S.value);
      }

      template <size_t N>
      static consteval Self constant(const char (&s)[N]) {
         const auto v = hex_to_words<W>(s);
         static_assert(v.size() == Self::N);

         // TODO: `return v * R2;`
         return Self(monty_mul(v, Self::R2, Self::P, Self::P_dash));
      }

      static consteval Self constant(int8_t x) {
         // TODO: `return x * R2;`

         std::array<W, N> v = {};
         v[0] = (x >= 0) ? x : -x;
         auto s = Self(monty_mul(v, Self::R2, Self::P, Self::P_dash));
         if(x < 0) {
            s = s.negate();
         }
         return s;
      }

   private:
      constexpr const std::array<W, N>& value() const { return m_val; }

      constexpr const W* ptr() const { return m_val.data(); }

      constexpr MontgomeryInteger(std::array<W, N> w) { m_val = w; }

      std::array<W, N> m_val;
};

template <StringLiteral PS>
void dump(const char* what, const MontgomeryInteger<PS>& fe) {
   std::cout << what << " = " << hex_encode(fe.serialize()) << "\n";
}

template <typename FieldElement>
class AffineCurvePoint {
   public:
      static const constinit size_t BYTES = 1 + 2 * FieldElement::BYTES;
      static const constinit size_t COMPRESSED_BYTES = 1 + FieldElement::BYTES;

      typedef AffineCurvePoint<FieldElement> Self;

      constexpr AffineCurvePoint(const FieldElement& x, const FieldElement& y) : m_x(x), m_y(y) {}

      constexpr AffineCurvePoint() : m_x(FieldElement::zero()), m_y(FieldElement::zero()) {}

      /*
      y**2 = x**3 + a*x + b

      y**2 - b = x**3 + a*x
      y**2 - b = (x**2 + a)*x
      */
      // ??????
      static constexpr Self identity() { return Self(FieldElement::zero(), FieldElement::zero()); }

      constexpr bool is_identity() const { return m_x.is_zero() && m_y.is_zero(); }

      AffineCurvePoint(const Self& other) = default;
      AffineCurvePoint(Self&& other) = default;
      AffineCurvePoint& operator=(const Self& other) = default;
      AffineCurvePoint& operator=(Self&& other) = default;

      constexpr Self negate() const { return Self(m_x, m_y.negate()); }

      constexpr std::array<uint8_t, Self::BYTES> serialize() const {
         std::array<uint8_t, Self::BYTES> r = {};
         BufferStuffer pack(r);
         pack.append(0x04);
         pack.append(m_x.serialize());
         pack.append(m_y.serialize());

         return r;
      }

      constexpr std::array<uint8_t, Self::COMPRESSED_BYTES> serialize_compressed() const {
         std::array<uint8_t, Self::COMPRESSED_BYTES> r = {};

         const bool y_is_even = y().is_even();

         BufferStuffer pack(r);
         pack.append(y_is_even ? 0x02 : 0x03);
         pack.append(x().serialize());

         return r;
      }

      //static constexpr Self deserialize(std::span<const uint8_t> bytes) {}

      constexpr const FieldElement& x() const { return m_x; }

      constexpr const FieldElement& y() const { return m_y; }

   private:
      FieldElement m_x;
      FieldElement m_y;
};

template <typename FieldElement, bool A_is_minus_3, bool A_is_zero>
class ProjectiveCurvePoint {
   public:
      static_assert(!(A_is_minus_3 && A_is_zero), "A param cannot be both 0 and -3");

      typedef ProjectiveCurvePoint<FieldElement, A_is_minus_3, A_is_zero> Self;
      typedef AffineCurvePoint<FieldElement> AffinePoint;

      static constexpr Self from_affine(const AffinePoint& pt) { return ProjectiveCurvePoint(pt.x(), pt.y()); }

      static constexpr Self identity() {
         return Self(FieldElement::zero(), FieldElement::zero(), FieldElement::zero());
      }

      constexpr ProjectiveCurvePoint() :
         m_x(FieldElement::zero()), m_y(FieldElement::zero()), m_z(FieldElement::zero()) {}

      constexpr ProjectiveCurvePoint(const FieldElement& x, const FieldElement& y) :
            m_x(x), m_y(y), m_z(FieldElement::one()) {}

      constexpr ProjectiveCurvePoint(const FieldElement& x, const FieldElement& y, const FieldElement& z) :
            m_x(x), m_y(y), m_z(z) {}

      ProjectiveCurvePoint(const Self& other) = default;
      ProjectiveCurvePoint(Self&& other) = default;
      ProjectiveCurvePoint& operator=(const Self& other) = default;
      ProjectiveCurvePoint& operator=(Self&& other) = default;

      friend constexpr Self operator+(const Self& a, const Self& b) { return Self::add(a, b); }

      friend constexpr Self operator+(const Self& a, const AffinePoint& b) { return Self::add_mixed(a, b); }

      friend constexpr Self operator+(const AffinePoint& a, const Self& b) { return Self::add_mixed(b, a); }

      friend constexpr Self operator-(const Self& a, const Self& b) { return a + b.negate(); }

      constexpr bool is_infinity() const { return z().is_zero(); }

      constexpr static Self add_mixed(const Self& a, const AffinePoint& b) {
         // fixme use proper mixed addition formula
         return Self::add(a, Self::from_affine(b));
      }

      constexpr static Self add(const Self& a, const Self& b) {
         //printf("add %d %d\n", a.is_infinity(), b.is_infinity());

         // TODO avoid these early returns by masking instead
         if(a.is_infinity()) {
            return b;
         }

         if(b.is_infinity()) {
            return a;
         }

         /*
         https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#addition-add-1998-cmo-2

         TODO detect a doubling!! DONE

         TODO rename these vars

         TODO reduce vars

         TODO take advantage of A = 0 and A = -3

         TODO use a complete addition formula??? (YES)
         https://eprint.iacr.org/2015/1060.pdf
         */

         const auto Z1Z1 = a.z().square();
         const auto Z2Z2 = b.z().square();
         const auto U1 = a.x() * Z2Z2;
         const auto U2 = b.x() * Z1Z1;
         const auto S1 = a.y() * b.z() * Z2Z2;
         const auto S2 = b.y() * a.z() * Z1Z1;
         const auto H = U2 - U1;
         const auto r = S2 - S1;

         if(H.is_zero()) {
            if(r.is_zero()) {
               return a.dbl();
            } else {
               return Self::identity();
            }
         }

         const auto HH = H.square();
         const auto HHH = H * HH;
         const auto V = U1 * HH;
         const auto t2 = r.square();
         const auto t3 = V + V;
         const auto t4 = t2 - HHH;
         const auto X3 = t4 - t3;
         const auto t5 = V - X3;
         const auto t6 = S1 * HHH;
         const auto t7 = r * t5;
         const auto Y3 = t7 - t6;
         const auto t8 = b.z() * H;
         const auto Z3 = a.z() * t8;

         return Self(X3, Y3, Z3);
      }

      constexpr Self dbl() const {
         /*
         https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
         */

         // FIXME is this specific to A == -3??

         const auto delta = z().square();
         const auto gamma = y().square();
         const auto beta = x() * gamma;
         const auto t0 = x() - delta;
         const auto t1 = x() + delta;
         const auto t2 = t0 * t1;
         const auto alpha = 3 * t2;
         const auto t3 = alpha.square();
         const auto t4 = 8 * beta;
         const auto X3 = t3 - t4;
         const auto t5 = y() + z();
         const auto t6 = t5.square();
         const auto t7 = t6 - gamma;
         const auto Z3 = t7 - delta;
         const auto t8 = 4 * beta;
         const auto t9 = t8 - X3;
         const auto t10 = gamma.square();
         const auto t11 = 8 * t10;
         const auto t12 = alpha * t9;
         const auto Y3 = t12 - t11;
         return Self(X3, Y3, Z3);
      }

      constexpr Self negate() const { return Self(m_x, m_y.negate(), m_z); }

      constexpr AffinePoint to_affine() const {
         if(m_z.is_one()) {
            return AffinePoint(m_x, m_y);
         }

         const auto z_inv = m_z.invert();
         const auto z2_inv = z_inv.square();
         const auto z3_inv = z_inv * z2_inv;

         const auto x = m_x * z2_inv;
         const auto y = m_y * z3_inv;
         return AffinePoint(x, y);
      }

      template <size_t N>
      static constexpr auto to_affine_batch(const std::array<Self, N>& projective) -> std::array<AffinePoint, N> {
         // Fixme use Montgomery's trick here

         std::array<AffinePoint, N> affine;

         for(size_t i = 0; i != N; ++i) {
            affine[i] = projective[i].to_affine();
         }

         return affine;
      }

      constexpr const FieldElement& x() const { return m_x; }

      constexpr const FieldElement& y() const { return m_y; }

      constexpr const FieldElement& z() const { return m_z; }

   private:
      FieldElement m_x;
      FieldElement m_y;
      FieldElement m_z;
};

// xxx
template <typename T>
concept ParamA = (std::same_as<T, const char*> || std::same_as<T, int8_t>);

template <typename C>
class PrecomputedMulTable {
   public:
      //static const constinit WINDOW_BITS = 1; // XXX allow config?

      //static_assert(WINDOW_BITS >= 1 && WINDOW_BITS <= 8);

      static const constinit size_t TABLE_SIZE = C::Scalar::BITS;

      constexpr PrecomputedMulTable(const typename C::AffinePoint& p) : m_table{} {
         std::array<typename C::ProjectivePoint, TABLE_SIZE> table;

         table[0] = C::ProjectivePoint::from_affine(p);
         for(size_t i = 1; i != TABLE_SIZE; ++i) {
            table[i] = table[i-1].dbl();
         }

         m_table = C::ProjectivePoint::to_affine_batch(table);
      }

      constexpr C::AffinePoint operator()(const C::Scalar& s) const {
         const auto bits = s.serialize();

         auto accum = C::ProjectivePoint::identity();

         for(size_t i = 0; i != C::Scalar::BITS; ++i) {
            const size_t b = C::Scalar::BITS - i - 1;

            const bool b_set = (bits[b / 8] >> (7 - b % 8)) & 1;

            if(b_set) {
               accum = accum + m_table[i];
            }
         }

         return accum.to_affine();
      }

   private:
      std::array<typename C::AffinePoint, TABLE_SIZE> m_table;
};

template <StringLiteral PS,
          StringLiteral AS,
          StringLiteral BS,
          StringLiteral NS,
          StringLiteral GXS,
          StringLiteral GYS,
          template <StringLiteral> typename FieldType = MontgomeryInteger>
class EllipticCurve {
   public:
      typedef MontgomeryInteger<NS> Scalar;
      typedef FieldType<PS> FieldElement;

      static const constexpr FieldElement A = FieldElement::constant(AS);
      static const constexpr FieldElement B = FieldElement::constant(BS);
      // ???
      //static const constexpr FieldElement N = FieldElement::constant(NS);
      static const constexpr FieldElement Gx = FieldElement::constant(GXS);
      static const constexpr FieldElement Gy = FieldElement::constant(GYS);

      static const constinit bool A_is_minus_3 = A == FieldElement::constant(-3);
      static const constinit bool A_is_zero = A == FieldElement::constant(0);

      typedef AffineCurvePoint<FieldElement> AffinePoint;
      typedef ProjectiveCurvePoint<FieldElement, A_is_zero, A_is_minus_3> ProjectivePoint;

      static const constexpr AffinePoint G = AffinePoint(Gx, Gy);
};

template <typename C>
C::AffinePoint scalar_mul(const typename C::AffinePoint& p,
                          const typename C::Scalar& s) {
   const auto bits = s.serialize();

   auto accum = C::ProjectivePoint::identity();
   auto pp = C::ProjectivePoint::from_affine(p);

   for(size_t i = 0; i != C::Scalar::BITS; ++i) {
      const size_t b = C::Scalar::BITS - i - 1;

      const bool b_set = (bits[b / 8] >> (7 - b % 8)) & 1;

      //accum.conditional_add(b_set, pp);
      if(b_set) {
         accum = accum + pp;
      }
      pp = pp.dbl();
   }

   return accum.to_affine();
}

}  // namespace Botan

int main() {
   using namespace Botan;

   //typedef MontgomeryInteger<"FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF"> fe;

#if 1
   typedef EllipticCurve<"FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF",
                         "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC",
                         "5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B",
                         "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551",
                         "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
                         "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5">
      P256;

   PrecomputedMulTable<P256> P256_mul(P256::G);

   auto s = P256::Scalar::zero();

   for(size_t i = 0; i != 10; ++i) {
      auto p = P256_mul(s);
      //auto p = scalar_mul<P256>(P256::G, s);
      std::cout << i << " -> " << hex_encode(p.serialize()) << "\n";
      s = s - P256::Scalar::one();
   }
   #endif
}
