from charm.toolbox.ecgroup import ECGroup, G, ZR
from charm.toolbox.pairinggroup import PairingGroup, G1, ZR
from charm.toolbox.integergroup import random
from trenc import TREnc, GS

from tools import ElGamal, DivProof

from functools import reduce

class PiInt():
    def __init__(self, group, number_bits):
        self.nb = number_bits
        self.group = group
        self.g = self.group.random(G)
        
        self.h0 = self.group.random(G) 
        self.h1 = self.group.random(G) 

        self.EG = ElGamal(self.group, self.g)
        self.epk, self.esk = self.EG.keygen()

        self.DivProof = DivProof(self.group, self.g, self.epk)

    def vote(self, m):
        assert len(m) == self.nb

        ballot = {}

        # Round 1
        alpha0 = self.group.random(ZR)
        alpha1 = self.group.random(ZR)
        t = self.group.random(ZR)

        com = (self.g ** t) * (self.h0 ** alpha0) * (self.h1 ** alpha1)
        ballot["com"] = com

        # Round 2
        ballot["c0"] = [0]*self.nb 
        ballot["c1"] = [0]*self.nb 
        ballot["pi"] = [0]*self.nb
        ballot["x"] = [0]*self.nb 
        ballot["y"] = [0]*self.nb

        for i in range(self.nb):
            # Round 2
            v0 = self.group.random(G)
            v1 = (self.g ** m[i])/v0

            ballot["c0"][i], r0 = self.EG.encrypt(self.epk, v0)
            ballot["c1"][i], r1 = self.EG.encrypt(self.epk, v1)

            c = [ballot["c0"][i][0]*ballot["c1"][i][0], ballot["c0"][i][1]*ballot["c1"][i][1]]
            r = r0 + r1
            x = m[i]
            statement = {"c": c}
            w = {"r": r, "x": x}
            ballot["pi"][i] = self.DivProof.ProveV(statement, w) 
        
            # Round 3
            ballot["x"][i] = alpha0*r0 + alpha1*r1
            ballot["y"][i] = v0**alpha0* v1**alpha1

        # Round 3
        ballot["t"] = t
        ballot["alpha0"] = alpha0
        ballot["alpha1"] = alpha1

        return ballot

    def verify(self, pk, ct):
        return True 

    def tally(self, pk, sk, ct):
        return 0

class PiIntLin():
    def __init__(self, group, number_bits, number_rounds):
        self.nb = number_bits
        self.group = group
        self.g = self.group.random(G)
       
        self.number_rounds = number_rounds

        self.EG = ElGamal(self.group, self.g)
        self.epk, self.esk = self.EG.keygen()

        self.DivProof = DivProof(self.group, self.g, self.epk)

    def vote(self, m):
        assert len(m) == self.nb

        ballot = {}

        # Setup round
        ballot["c"] = [0]*self.nb 
        ballot["pi"] = [0]*self.nb

        for i in range(self.nb):
            v = (self.g ** m[i])
            ballot["c"][i], r = self.EG.encrypt(self.epk, v)

            statement = {"c": ballot["c"][i]}
            w = {"r": r, "x": m[i]}
            ballot["pi"][i] = self.DivProof.ProveV(statement, w) 
        

        ballot["c0"] = [[0 for j in range(self.number_rounds)] for i in range(self.nb)]
        ballot["c1"] = [[0 for j in range(self.number_rounds)] for i in range(self.nb)]
        ballot["b"] = [[0 for j in range(self.number_rounds)] for i in range(self.nb)]
        ballot["v"] = [[0 for j in range(self.number_rounds)] for i in range(self.nb)]
        ballot["z"] = [[0 for j in range(self.number_rounds)] for i in range(self.nb)]
       
        for j in range(self.number_rounds):
            b = int(random(2))
            for i in range(self.nb):
                v = [0, 0]
                v[0] = self.group.random(G)
                v[1] = (self.g ** m[i])/v[0]
                
                r = [0, 0]
                ballot["c0"][i][j], r[0] = self.EG.encrypt(self.epk, v[0])
                ballot["c1"][i][j], r[1] = self.EG.encrypt(self.epk, v[1])

                ballot["b"][i][j] = b
                ballot["v"][i][j] = v[ballot["b"][i][j]]
                ballot["z"][i][j] = r[ballot["b"][i][j]]

        return ballot

    def verify(self, pk, ct):
        return True 

    def tally(self, pk, sk, ct):
        return 0

class PiNonInt():
    def __init__(self, group, number_bits):
        self.nb = number_bits
        self.group = group
        
        self.Trenc = TREnc(self.group)
        self.epk, self.esk = self.Trenc.keygen()
        
        self.GS = GS(self.group)

    def register(self):
        credentials = {}
        credentials["alpha0"] = self.group.random(ZR)
        credentials["alpha1"] = self.group.random(ZR)
        credentials["lk"] = self.Trenc.lgen(self.epk)

        return credentials 

    def vote(self, credentials, m):
        assert len(m) == self.nb

        alpha0 = credentials["alpha0"]
        alpha1 = credentials["alpha1"]
        lk = credentials["lk"]

        g = self.epk["g"]
        g_hat = self.epk["g_hat"]
        h = self.epk["h"]
        h_hat = self.epk["h_hat"]
        f = self.epk["f"]

        ballot = {}
        ballot["c0"] = [0]*self.nb 
        ballot["c1"] = [0]*self.nb 
        ballot["y"]  = [0]*self.nb 
        ballot["pi"] = [0]*self.nb

        for i in range(self.nb):
            v0 = self.group.random(G1)
            v1 = (g ** m[i])/v0
            y = (v0 ** alpha0) * (v1 ** alpha1)

            ballot["c0"][i], r0 = self.Trenc.lenc(self.epk, lk, v0)
            ballot["c1"][i], r1 = self.Trenc.lenc(self.epk, lk, v1)
            r = r0 + r1
    
            # Compute pi 
            crs = self.GS.gen()
            C_M, R_M = self.GS.com1(crs, g ** m[i]) 
            C_hat_M, S_M = self.GS.com2(crs, g_hat ** m[i])
            C_hat_r, S_r = self.GS.com2(crs, g_hat ** r)
            C_hat_g, S_g = self.GS.com2(crs, g_hat)

            c0 = ballot["c0"][i]["c"][0] * ballot["c1"][i]["c"][0]
            c1 = ballot["c0"][i]["c"][1] * ballot["c1"][i]["c"][1]
            c2 = ballot["c0"][i]["c"][2] * ballot["c1"][i]["c"][2]

            pi_0 = self.GS.prove_pairing_linear_2([c0, g ** -1, f ** -1], [S_g, S_M, S_r])
            pi_1 = self.GS.prove_pairing_linear_2([c1, g ** -1], [S_g, S_r])
            pi_2 = self.GS.prove_pairing_linear_2([c2, h ** -1], [S_g, S_r])
            
            pi_01_1 = self.GS.prove_pairing_quadratic(crs, [g ** m[i]], [g_hat ** m[i]], [g], [1], [[-1]], [R_M], [S_M])
            pi_01_2 = self.GS.prove_pairing_quadratic(crs, [g ** m[i]], [g_hat ** m[i]], [g], [g_hat], [[0]], [R_M], [S_M])
            ballot["pi"] = [pi_0, pi_1, pi_2, pi_01_1, pi_01_2]
        return ballot

    def verify(self, pk, ct):
        return True 

    def tally(self, pk, sk, ct):
        return 0
