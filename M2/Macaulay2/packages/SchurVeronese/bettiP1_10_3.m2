--This file computes Betti tables for P^1 for d = 10 and b = 3
A := degreesRing 2
new HashTable from {
--tb stands for Total Betti numbers
"tb"=>new HashTable from {(7,0) => 0, (6,1) => 360, (7,1) => 180, (8,0) => 0, (8,1) => 50, (9,0) => 0, (9,1) => 6, (0,0) => 4, (0,1) => 0, (1,0) => 30, (2,0) => 90, (1,1) => 0, (3,0) => 120, (2,1) => 0, (4,0) => 0, (3,1) => 0, (5,0) => 0, (4,1) => 252, (5,1) => 420, (6,0) => 0},
--mb stands for Multigraded Betti numbers
"mb"=>new HashTable from {(7,0) => 0, (6,1) => A_0^48*A_1^25+2*A_0^47*A_1^26+4*A_0^46*A_1^27+6*A_0^45*A_1^28+9*A_0^44*A_1^29+12*A_0^43*A_1^30+16*A_0^42*A_1^31+20*A_0^41*A_1^32+24*A_0^40*A_1^33+27*A_0^39*A_1^34+29*A_0^38*A_1^35+30*A_0^37*A_1^36+30*A_0^36*A_1^37+29*A_0^35*A_1^38+27*A_0^34*A_1^39+24*A_0^33*A_1^40+20*A_0^32*A_1^41+16*A_0^31*A_1^42+12*A_0^30*A_1^43+9*A_0^29*A_1^44+6*A_0^28*A_1^45+4*A_0^27*A_1^46+2*A_0^26*A_1^47+A_0^25*A_1^48, (8,0) => 0, (7,1) => A_0^51*A_1^32+2*A_0^50*A_1^33+4*A_0^49*A_1^34+6*A_0^48*A_1^35+8*A_0^47*A_1^36+10*A_0^46*A_1^37+12*A_0^45*A_1^38+14*A_0^44*A_1^39+16*A_0^43*A_1^40+17*A_0^42*A_1^41+17*A_0^41*A_1^42+16*A_0^40*A_1^43+14*A_0^39*A_1^44+12*A_0^38*A_1^45+10*A_0^37*A_1^46+8*A_0^36*A_1^47+6*A_0^35*A_1^48+4*A_0^34*A_1^49+2*A_0^33*A_1^50+A_0^32*A_1^51, (9,0) => 0, (8,1) => A_0^53*A_1^40+2*A_0^52*A_1^41+3*A_0^51*A_1^42+4*A_0^50*A_1^43+5*A_0^49*A_1^44+5*A_0^48*A_1^45+5*A_0^47*A_1^46+5*A_0^46*A_1^47+5*A_0^45*A_1^48+5*A_0^44*A_1^49+4*A_0^43*A_1^50+3*A_0^42*A_1^51+2*A_0^41*A_1^52+A_0^40*A_1^53, (9,1) => A_0^54*A_1^49+A_0^53*A_1^50+A_0^52*A_1^51+A_0^51*A_1^52+A_0^50*A_1^53+A_0^49*A_1^54, (0,0) => A_0^3+A_0^2*A_1+A_0*A_1^2+A_1^3, (0,1) => 0, (1,0) => A_0^12*A_1+2*A_0^11*A_1^2+3*A_0^10*A_1^3+3*A_0^9*A_1^4+3*A_0^8*A_1^5+3*A_0^7*A_1^6+3*A_0^6*A_1^7+3*A_0^5*A_1^8+3*A_0^4*A_1^9+3*A_0^3*A_1^10+2*A_0^2*A_1^11+A_0*A_1^12, (2,0) => A_0^20*A_1^3+2*A_0^19*A_1^4+3*A_0^18*A_1^5+4*A_0^17*A_1^6+5*A_0^16*A_1^7+6*A_0^15*A_1^8+7*A_0^14*A_1^9+8*A_0^13*A_1^10+9*A_0^12*A_1^11+9*A_0^11*A_1^12+8*A_0^10*A_1^13+7*A_0^9*A_1^14+6*A_0^8*A_1^15+5*A_0^7*A_1^16+4*A_0^6*A_1^17+3*A_0^5*A_1^18+2*A_0^4*A_1^19+A_0^3*A_1^20, (1,1) => 0, (2,1) => 0, (3,0) => A_0^27*A_1^6+A_0^26*A_1^7+2*A_0^25*A_1^8+3*A_0^24*A_1^9+4*A_0^23*A_1^10+5*A_0^22*A_1^11+7*A_0^21*A_1^12+8*A_0^20*A_1^13+9*A_0^19*A_1^14+10*A_0^18*A_1^15+10*A_0^17*A_1^16+10*A_0^16*A_1^17+10*A_0^15*A_1^18+9*A_0^14*A_1^19+8*A_0^13*A_1^20+7*A_0^12*A_1^21+5*A_0^11*A_1^22+4*A_0^10*A_1^23+3*A_0^9*A_1^24+2*A_0^8*A_1^25+A_0^7*A_1^26+A_0^6*A_1^27, (3,1) => 0, (4,0) => 0, (4,1) => A_0^39*A_1^14+A_0^38*A_1^15+2*A_0^37*A_1^16+3*A_0^36*A_1^17+5*A_0^35*A_1^18+7*A_0^34*A_1^19+9*A_0^33*A_1^20+11*A_0^32*A_1^21+14*A_0^31*A_1^22+16*A_0^30*A_1^23+18*A_0^29*A_1^24+19*A_0^28*A_1^25+20*A_0^27*A_1^26+20*A_0^26*A_1^27+19*A_0^25*A_1^28+18*A_0^24*A_1^29+16*A_0^23*A_1^30+14*A_0^22*A_1^31+11*A_0^21*A_1^32+9*A_0^20*A_1^33+7*A_0^19*A_1^34+5*A_0^18*A_1^35+3*A_0^17*A_1^36+2*A_0^16*A_1^37+A_0^15*A_1^38+A_0^14*A_1^39, (5,0) => 0, (6,0) => 0, (5,1) => A_0^44*A_1^19+2*A_0^43*A_1^20+3*A_0^42*A_1^21+5*A_0^41*A_1^22+8*A_0^40*A_1^23+11*A_0^39*A_1^24+15*A_0^38*A_1^25+19*A_0^37*A_1^26+23*A_0^36*A_1^27+27*A_0^35*A_1^28+30*A_0^34*A_1^29+32*A_0^33*A_1^30+34*A_0^32*A_1^31+34*A_0^31*A_1^32+32*A_0^30*A_1^33+30*A_0^29*A_1^34+27*A_0^28*A_1^35+23*A_0^27*A_1^36+19*A_0^26*A_1^37+15*A_0^25*A_1^38+11*A_0^24*A_1^39+8*A_0^23*A_1^40+5*A_0^22*A_1^41+3*A_0^21*A_1^42+2*A_0^20*A_1^43+A_0^19*A_1^44},
--sb represents the betti numbers as sums of Schur functors
"sb"=>new HashTable from {(7,0) => {}, (6,1) => {({48,25},1)}, (7,1) => {({51,32},1)}, (8,0) => {}, (8,1) => {({53,40},1)}, (9,0) => {}, (9,1) => {({54,49},1)}, (0,0) => {({3,0},1)}, (0,1) => {}, (1,0) => {({12,1},1)}, (2,0) => {({20,3},1)}, (1,1) => {}, (3,0) => {({27,6},1)}, (2,1) => {}, (4,0) => {}, (3,1) => {}, (5,0) => {}, (4,1) => {({39,14},1)}, (5,1) => {({44,19},1)}, (6,0) => {}},
--dw encodes the dominant weights in each entry
"dw"=>new HashTable from {(7,0) => {}, (6,1) => {{48,25}}, (7,1) => {{51,32}}, (8,0) => {}, (8,1) => {{53,40}}, (9,0) => {}, (9,1) => {{54,49}}, (0,0) => {{3,0}}, (0,1) => {}, (1,0) => {{12,1}}, (2,0) => {{20,3}}, (1,1) => {}, (3,0) => {{27,6}}, (2,1) => {}, (4,0) => {}, (3,1) => {}, (5,0) => {}, (4,1) => {{39,14}}, (5,1) => {{44,19}}, (6,0) => {}},
--lw encodes the lex leading weight in each entry
"lw"=>new HashTable from {(7,0) => {}, (6,1) => {48,25}, (7,1) => {51,32}, (8,0) => {}, (8,1) => {53,40}, (9,0) => {}, (9,1) => {54,49}, (0,0) => {3,0}, (0,1) => {}, (1,0) => {12,1}, (2,0) => {20,3}, (1,1) => {}, (3,0) => {27,6}, (2,1) => {}, (4,0) => {}, (3,1) => {}, (5,0) => {}, (4,1) => {39,14}, (5,1) => {44,19}, (6,0) => {}},
--nr encodes the number of disctinct reprsentations in each entry
"nr"=>new HashTable from {(7,0) => 0, (6,1) => 1, (7,1) => 1, (8,0) => 0, (8,1) => 1, (9,0) => 0, (9,1) => 1, (0,0) => 1, (0,1) => 0, (1,0) => 1, (2,0) => 1, (1,1) => 0, (3,0) => 1, (2,1) => 0, (4,0) => 0, (3,1) => 0, (5,0) => 0, (4,1) => 1, (5,1) => 1, (6,0) => 0},
--nrm encodes the number of representations with multiplicity in each entry
"nrm"=>new HashTable from {(7,0) => 0, (6,1) => 1, (7,1) => 1, (8,0) => 0, (8,1) => 1, (9,0) => 0, (9,1) => 1, (0,0) => 1, (0,1) => 0, (1,0) => 1, (2,0) => 1, (1,1) => 0, (3,0) => 1, (2,1) => 0, (4,0) => 0, (3,1) => 0, (5,0) => 0, (4,1) => 1, (5,1) => 1, (6,0) => 0},
--er encodes the errors in the computed multigraded Hilbert series via our Schur method in each entry
"er"=>new HashTable from {(7,0) => 0, (6,1) => 360, (7,1) => 180, (8,0) => 0, (8,1) => 50, (9,0) => 0, (9,1) => 6, (0,0) => 4, (0,1) => 0, (1,0) => 30, (2,0) => 90, (1,1) => 0, (3,0) => 120, (2,1) => 0, (4,0) => 0, (3,1) => 0, (5,0) => 0, (4,1) => 252, (5,1) => 420, (6,0) => 0},
--bs encodes the Boij-Soederberg coefficients each entry
"bs"=>{3628800/1},
}
