#include <stdio.h>

typedef unsigned int  uint;
typedef unsigned char byte;
typedef unsigned long long qword;

const byte statemap[][7] = {
  {  7,  0,  8,  9,  8,  8,  8, },
  {  7,  0,  8,  9,  8,  8,  8, },
  {  7,  0,  8,  9,  8,  8,  8, },
  {  7,  0,  8,  9,  8,  8,  8, },
  {  7,  1,  8,  9,  8,  8,  8, },
  {  7,  2,  8,  9,  8,  8,  8, },
  {  7,  3,  8,  9,  8,  8,  8, },
  { 10,  4, 11, 11, 11, 11, 11, },
  { 10,  5, 11, 11, 11, 11, 11, },
  { 10,  6, 11, 11, 11, 11, 11, },
  { 10,  4, 11, 11, 11, 11, 11, },
  { 10,  5, 11, 11, 11, 11, 11, },
};

struct lzma_decode {

  enum { SCALElog=11, SCALE=1<<SCALElog, hSCALE=SCALE/2 };

  struct Counter {
    short P;
    Counter() { P = hSCALE; }
    void Update( uint bit ) { P += bit ? -(P>>5) : ((SCALE-P)>>5); }
  };

  FILE *f, *g;
  byte get( void ) { return getc(f); }
  void put( uint c ) { putc(c,g); }

  uint range, code;

  void rc_Init( void ) {
    code = get() | ((get()<<24) | (get()<<16) | (get()<<8) | (get()));
    range = 0xFFFFFFFF;
  }

  uint rc_Bits( uint l ) {
    uint x=0; do {
      if( range<0x01000000 ) range<<=8, code=(code<<8) | get();
      range &= ~1;
      uint rnew = (range>>1) * 1;
      uint bit = code >= rnew;
      range = bit ? code-=rnew,range-rnew : rnew;
      x += x + bit; 
    } while( --l!=0 );
    return x;
  }

  uint rc_Decode( uint P ) {
    if( range<0x01000000 ) range<<=8, code=(code<<8) | get();
    uint rnew = (range >> SCALElog) * P; 
    uint bit = code >= rnew;
    range = bit ? code-=rnew,range-rnew : rnew;
    return bit;
  }

  uint BIT( Counter& cc ) { 
    uint bit = rc_Decode(cc.P);
    cc.Update( bit );
    return bit; 
  }

  enum {
    kNumLPosBitsMax = 4,
    kNumPosBitsMax  = 4, kNumPosStatesMax = (1<<kNumPosBitsMax),
    kLenNumLowBits  = 3, kLenNumLowSymbols = (1<<kLenNumLowBits),
    kLenNumMidBits  = 3, kLenNumMidSymbols = (1<<kLenNumMidBits),
    kLenNumHighBits = 8, kLenNumHighSymbols = (1<<kLenNumHighBits),
    kStartPosModelIndex = 4, kEndPosModelIndex = 14, 
    kNumFullDistances = (1<<(kEndPosModelIndex>>1)),
    kNumPosSlotBits = 6, kNumLenToPosStates = 4,
    kNumAlignBits   = 4, kAlignTableSize = (1<<kNumAlignBits),
    kMatchMinLen    = 2, kNumLitStates = 7, kNumStates = 12,
    id_match=0, id_lit,id_r0,id_litr0, id_r1,id_r2,id_r3
  };

  byte* dic;
  uint lc, lp, pb, dictSize;
  qword f_len;
  byte rbit5[32];

  Counter c_IsMatch[kNumStates][1<<kNumPosBitsMax];
  Counter c_IsRep[kNumStates];
  Counter c_IsRepG0[kNumStates];
  Counter c_IsRepG1[kNumStates];
  Counter c_IsRepG2[kNumStates];
  Counter c_IsRep0Long[kNumStates][1<<kNumPosBitsMax];
  Counter c_LenChoice[2];
  Counter c_LenChoice2[2];
  Counter c_Literal[1<<kNumLPosBitsMax][256][3][256];
  Counter c_LenLow[2][kNumPosStatesMax][1<<kLenNumLowBits];
  Counter c_LenMid[2][kNumPosStatesMax][1<<kLenNumMidBits];
  Counter c_LenHigh[2][1<<kLenNumHighBits];
  Counter c_PosSlot[kNumLenToPosStates][1<<kNumPosSlotBits];
  Counter c_SpecPos[kNumFullDistances-kEndPosModelIndex];
  Counter c_Align[1<<kNumAlignBits];

  lzma_decode( FILE* _f, FILE* _g ) {

    f=_f; g=_g;
    byte d = get(); // lc/pb/lp byte first
    dictSize = get() | (get()<<8) | (get()<<16) | (get()<<24);
    dic = new byte[dictSize];
    f_len = 0;
    uint i; for( i=0; i<8; i++ ) f_len = (f_len>>8) | (qword(get())<<56);
    rc_Init();
    lc = d % 9; d /= 9;
    pb = d / 5; lp = d % 5;

    for( i=0; i<32; i++ ) rbit5[i] = ((i*0x0802&0x22110)|(i*0x8020&0x88440))*0x10101 >> 16+3;

    uint state=0,rep0=1,rep1=1,rep2=1,rep3=1;
    uint dicPos = 0, dicBufSize = dictSize;
    uint pbMask = (1<<pb)-1, lpMask = (1<<lp)-1, lc8 = 8-lc;
    uint id, val, sym=0, i_len, dist, pos, len, cps;
    Counter* clen = 0;

    for( qword filepos=0; filepos<f_len; state=statemap[state][id] ) {

      uint posState = filepos & pbMask;
      uint psym = byte(sym);
      #define rep0pos() (dicPos-rep0) + ((dicPos<rep0) ? dicBufSize : 0)
      #define symstore(sym) { dic[dicPos]=sym; if( ++dicPos==dicBufSize ) dicPos=0; put(sym); filepos++; }

      if( BIT(c_IsMatch[state][posState])==0 ) id=id_lit; else
        if( BIT(c_IsRep[state])==0 ) id=id_match; else
          if( BIT(c_IsRepG0[state])==0 )
            if( BIT(c_IsRep0Long[state][posState])==0 ) id=id_litr0; else id=id_r0;
          else
            if( BIT(c_IsRepG1[state])==0 ) id=id_r1; else
              if( BIT(c_IsRepG2[state]) ) id=id_r3; else id=id_r2;

      if( (id==id_lit) || (id==id_litr0) ) { // decode a literal?

        if( id==id_litr0 ) sym = dic[rep0pos()]; else {
          Counter (&cc)[3][256] = c_Literal[filepos&lpMask][psym>>lc8];

          if( state>=kNumLitStates ) {
            uint matchbyte = 0x100 + dic[rep0pos()];
            for( sym=1; sym<0x100; ) {
              uint mbprefix = (matchbyte<<=1) >> 8;
              sym += sym + BIT(cc[1+(mbprefix&1)][sym]);
              if( mbprefix!=sym ) break;
            }
          } else sym=1;
          for(; sym<0x100; sym+=sym+BIT(cc[0][sym]) );
        }

        symstore(sym);

      } else {

        uint f_rep = (id!=id_match);

        if( f_rep ) {
          if( id!=id_r0 ) {
            dist = rep1;
            if( id!=id_r1 ) {
              dist = rep2;
              if( id==id_r3 ) dist = rep3, rep3 = rep2;
              rep2 = rep1;
            }
            rep1 = rep0; rep0 = dist;
          }
        }

        if( BIT(c_LenChoice[f_rep])==0 ) i_len=0; else
          if( BIT(c_LenChoice2[f_rep])==0 ) i_len=1; else i_len=2;

        uint limit, offset;
        if( i_len==0 ) {
          clen = &c_LenLow[f_rep][posState][0];
          offset = 0; limit = (1 << kLenNumLowBits);
        } else {
          if( i_len==1 ) {
            clen = &c_LenMid[f_rep][posState][0];
            offset = kLenNumLowSymbols; limit = (1<<kLenNumMidBits);
          } else {
            clen = &c_LenHigh[f_rep][0];
            offset = kLenNumLowSymbols + kLenNumMidSymbols; limit = (1<<kLenNumHighBits);
          }
        }

        for( len=1; len<limit; len+=len + BIT(clen[len]) );
        len -= limit; 
        len += offset;

        if( f_rep==0 ) {

          Counter (&cpos)[1<<kNumPosSlotBits] = c_PosSlot[len<kNumLenToPosStates?len:kNumLenToPosStates-1];

          for( dist=1; dist<64; dist+=dist + BIT(cpos[dist]) ); dist -= 64;

          if( dist>=kStartPosModelIndex ) {
            uint posSlot = dist;
            int numDirectBits = (dist>>1) - 1; // 13/2-1=5 max
            dist = (2 | (dist & 1));

            if( posSlot<kEndPosModelIndex ) {

              dist <<= numDirectBits;
              uint limit = 1<<numDirectBits;
              for( i=1; i<limit; i+=i + BIT(c_SpecPos[dist-posSlot-1+i]) );
              dist += rbit5[ (i-limit)<<(5-numDirectBits) ];

            } else {

              numDirectBits -= kNumAlignBits;
              (dist<<=numDirectBits) += rc_Bits(numDirectBits);
              for( i=1; i<16; i+=i + BIT(c_Align[i]) );
              (dist <<= kNumAlignBits) += rbit5[(i-16)<<1];
              if( dist==0xFFFFFFFFU ) break; // EOF?
            }
          }
          rep3=rep2; rep2=rep1; rep1=rep0; rep0=dist+1;
        } // dist

        for( pos=rep0pos(),len+=kMatchMinLen; len>0; len-- ) {
          sym = dic[pos]; symstore(sym);
          if( ++pos == dicBufSize ) pos=0;
        }

      } // match

    } // for

  }

};

int main( int argc, char** argv ) {
  if( argc<3 ) return 1;
  FILE* f = fopen( argv[1], "rb" ); if( f==0 ) return 2;
  FILE* g = fopen( argv[2], "wb" ); if( g==0 ) return 3;

  static lzma_decode D( f, g );

  fclose( f );
  fclose( g );
  return 0;
}
