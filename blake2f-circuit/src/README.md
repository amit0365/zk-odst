Function Compress
   Input:
      h                      Persistent state vector
      chunk                  128-byte (16 double word) chunk of message to compress
      t: Number, 0..2128     Count of bytes that have been fed into the Compression
      IsLastBlock: Boolean   Indicates if this is the final round of compression
   Output:
      h                      Updated persistent state vector

   Setup local work vector V
   V0..7 ← h0..7   First eight items are copied from persistent state vector h
   V8..15 ← IV0..7 Remaining eight items are initialized from the IV

   circuit layout // Todo complete

        |         | s1  |  s2 |  s3 |  s4 |  s5 |
        | V0..7   |  1  |  0  |  0  |  0  |  0  |
        | V8..15  |  0  |  1  |  0  |  0  |  0  |
        | V12     |  0  |  0  |  1  |  0  |  0  |
        | V13     |  0  |  0  |  0  |  1  |  0  |
        | V14     |  0  |  0  |  0  |  0  |  1  |


   Mix the 128-bit counter t into V12:V13
   V12 ← V12 xor Lo(t)    Lo 64-bits of UInt128 t
   V13 ← V13 xor Hi(t)    Hi 64-bits of UInt128 t
  
   If this is the last block then invert all the bits in V14
   if IsLastBlock then
      V14 ← V14 xor 0xFFFFFFFFFFFFFFFF
   
   Treat each 128-byte message chunk as sixteen 8-byte (64-bit) words m
   m0..15 ← chunk  
   // is decomposition check really required? or can be done by just splitting of words into chunks?
   // Todo implement decomposition of message into chunks see 0xparc tutorials and 
   // and decomposition gadget here: https://zcash.github.io/halo2/design/gadgets/decomposition.html


   // Todo mixing circuit



   Twelve rounds of cryptographic message mixing
   for i from 0 to 11 do
      Select message mixing schedule for this round.
       BLAKE2b uses 12 rounds, while SIGMA has only 10 entries.
      S0..15 ← SIGMA[i mod 10]   Rounds 10 and 11 use SIGMA[0] and SIGMA[1] respectively

      Mix(V0, V4, V8,  V12, m[S0], m[S1])
      Mix(V1, V5, V9,  V13, m[S2], m[S3])
      Mix(V2, V6, V10, V14, m[S4], m[S5])
      Mix(V3, V7, V11, V15, m[S6], m[S7])

      Mix(V0, V5, V10, V15, m[S8],  m[S9])
      Mix(V1, V6, V11, V12, m[S10], m[S11])
      Mix(V2, V7, V8,  V13, m[S12], m[S13])
      Mix(V3, V4, V9,  V14, m[S14], m[S15])
      
   end for

   Mix the upper and lower halves of V into ongoing state vector h
   h0..7 ← h0..7 xor V0..7
   h0..7 ← h0..7 xor V8..15

   Result ← h
End Function Compress


Mix(V0, V4, V8,  V12, m[S0], m[S1])

(V0, V4, V8,  V12, m[S0], m[S1]) -> Va, Vb, Vc, Vd , x: message chunks, y : message chunks

Function Mix
   Inputs:
        Va, Vb, Vc, Vd       four 8-byte word entries from the work vector V
        x, y                 two  8-byte word entries from padded message m
   Output:
        Va, Vb, Vc, Vd       the modified versions of Va, Vb, Vc, Vd

   // decompose a,b,c,d in ABCDvar
   Va1 ←  Va + Vb + x          with input
   Vd1 ← (Vd xor Va1) rotate right 32

   Vc1 ← Vc + Vd1              no input
   // decompose b and c1 in EFGHvar
   Vb1 ← (Vb xor Vc1) rotate right 24

   // decompose a1,b1,c1,d1 in ABCDvar
   Va2 ← Va1 + Vb1 + y          with input
   Vd2 ← (Vd1 xor Va2) rotate right 16

   Vc2 ← Vc1 + Vd2             no input
   // decompose b1 and c2 in IJKLvar
   Vb2 ← (Vb1 xor Vc2) rotate right 63

   Result ← Va, Vb, Vc, Vd
End Function Mix



// each chunk is correctly range-checked

// final gate call in subregion
// compression util - assign row values and copy constraints, calculates R0 even and odd
// compression - creates gate and assign columns a3, a4, a5
// compression_gate - define gate operations
// compression_util has decompose E into efgh 
// subregion_initial has decompose A, B, C and assigns D and H


// R0 even and odd are used for sigma gates
// P, Q are used for ch gates
// M is used for majority gate

// for some reason assign outputs for sigma is defined in table16
// while the assign outputs of other gates are in compression_util
// which uses assign spread outputs from table16

// test in table16

// how the already known spread values are called/used?

// are these used for every lookup in a gate? we already have some lookup values
//   let a_0 = lookup.tag;
//   let a_1 = lookup.dense;
//   let a_2 = lookup.spread;
//   a7 and a8 are used for word hi and lo values 
//   we need four word values so total 8, in decompose_abcd

// how decompose_efgh and decompose_e work?

// ask halo2 discord if word lo hi required in decompose abcd