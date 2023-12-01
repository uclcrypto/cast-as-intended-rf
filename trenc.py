from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT
from charm.toolbox.PKSig import PKSig
from charm.toolbox.PKEnc import PKEnc

from tools import GS, LHSP
from functools import reduce

class TREnc(PKEnc):
    def __init__(self, group):
        PKEnc.__init__(self)
        self.group = group 
        self.e_1 = self.group.init(G1)
        self.e_2 = self.group.init(G2)
        self.e_t = self.group.init(GT)
        
        self.GS = GS(self.group)
    
    def keygen(self, bit_by_bit = True):
        g = self.group.random(G1)
        h = self.group.random(G1)
        g_hat = self.group.random(G2)
        h_hat = self.group.random(G2)
        
        # Step 1
        alpha = self.group.random(ZR)
        beta  = self.group.random(ZR)
        f = (g ** alpha) * (h ** beta) 
        
        # Step 2
        delta = self.group.random(ZR)
        F = f ** delta 
        G = g ** delta 
        H = h ** delta 

        # Step 3
        crs_w = self.GS.gen()
        
        # Step 4
        lhsp = LHSP(2, {"group": self.group, "g_hat": g_hat, "h_hat": h_hat})

        pku, sku = lhsp.keygen()
        pkv, skv = lhsp.keygen()
       
        Su = lhsp.sign(pku, sku, [g, h])
        Sv = lhsp.sign(pkv, skv, [g, h])

        sk = {"alpha": alpha, "beta": beta}
        pk = {"f": f, "g": g, "h": h, "F": F, "G": G, "crs_w": crs_w, "Su": Su,
                "Sv": Sv, "g_hat": g_hat, "h_hat": h_hat}
        return pk, sk
    
    def lgen(self, pk):
        lhsp = LHSP(3, {"group": self.group, "g_hat": pk["g_hat"], "h_hat": pk["h_hat"]})
        opk, osk = lhsp.keygen()
        return {"osk": osk, "opk": opk}

    def lenc(self, pk, lk, m):
        lhsp = LHSP(3, {"group": self.group, "g_hat": pk["g_hat"], "h_hat": pk["h_hat"]})
        gs = GS(self.group)

        f = pk["f"]
        g = pk["g"]
        h = pk["h"]
        F = pk["F"]
        G = pk["G"]
        Su = pk["Su"]
        Sv = pk["Sv"]
        crs_w = pk["crs_w"]
        g_hat = pk["g_hat"]
        h_hat = pk["h_hat"]

        # Step 1
        theta = self.group.random(ZR)
        c0 = m * f ** theta
        c1 = g ** theta
        c2 = h ** theta
    
        # Step 2
        opk, osk = lk["opk"], lk["osk"]
        sigma_1 = lhsp.sign(opk, osk, [g, c0, c1])
        sigma_2 = lhsp.sign(opk, osk, [1, f, g])
        sigma_3 = lhsp.sign(opk, osk, [1, F, G])

        # Step 3
        C_Z, R_Z = gs.com1(crs_w, sigma_1["Z"])
        C_R, R_R = gs.com1(crs_w, sigma_1["R"])
        pi_hat_sig = gs.prove_pairing_linear_1([g_hat, h_hat], [R_Z, R_R])

        # Step 4
        tau = self.group.random(ZR)
        pi_ss = {}
        pi_ss["Z"] = Su["Z"] ** tau * Sv["Z"] 
        pi_ss["R"] = Su["R"] ** tau * Sv["R"] 
        
        ct = {"c": [c0, c1, c2], "C_Z": C_Z, "C_R": C_R, "sigma_2": sigma_2,
                "sigma_3": sigma_3, "pi_ss": pi_ss, "pi_hat_sig": pi_hat_sig,
                "opk": opk}
        return ct, theta

    def encrypt(self, pk, m, bit_by_bit = True):
        assert len(m) == self.lb
        
        lk = self.lgen(pk)
        ct = self.lenc(pk, lk, m, bit_by_bit)
        return ct
    
    def verify(self, pk, ct): 
        return True

    def decrypt(self, pk, sk, ct):
        if not self.verify(pk, ct):
            return "bot" 
        else:
            if ct["c"][2][i] == ct["c"][0]**sk["alpha_i"][i] * ct["c"][1]**sk["beta_i"][i]:
                m = 0
            elif ct["c"][2][i] == self.g * ct["c"][0]**sk["alpha_i"][i] * ct["c"][1]**sk["beta_i"][i]:
                m = 1 
            return m
