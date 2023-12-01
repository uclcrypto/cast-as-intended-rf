from protocols import PiInt, PiIntLin, PiNonInt
from charm.toolbox.pairinggroup import PairingGroup
from charm.toolbox.ecgroup import ECGroup
from charm.toolbox.eccurve import secp224r1,secp256k1

pairing_group = PairingGroup("BN254")
ec_group = ECGroup(secp224r1)
ec_group = ECGroup(secp256k1)

assert ec_group.InitBenchmark(), "failed to initialize benchmark"
assert pairing_group.InitBenchmark(), "failed to initialize benchmark"

n_run = 100

# Pi_1
print("Interactive protocol with constant number of rounds")
for k in [1, 2, 4, 8, 32]:
    scheme = PiInt(ec_group, k)
    #pk, sk = scheme.setup()
    m = [i%2 for i in range(k)]
    ec_group.StartBenchmark(["CpuTime"])
    for i in range(n_run):
        scheme.vote(m)
    ec_group.EndBenchmark()

    print(k)
    msmtDict = ec_group.GetGeneralBenchmarks()
    print("<=== General Benchmarks ===>")
    print("Cpu time := ", msmtDict["CpuTime"]/n_run)

# Pi_2
print("Interactive protocol with linear number of rounds")
for k in [1, 2, 4, 8, 32]:
    scheme = PiIntLin(ec_group, k, number_rounds = 16)
    #pk, sk = scheme.setup()
    m = [i%2 for i in range(k)]
    ec_group.StartBenchmark(["CpuTime"])
    for i in range(n_run):
        scheme.vote(m)
    ec_group.EndBenchmark()

    print(k)
    msmtDict = ec_group.GetGeneralBenchmarks()
    print("<=== General Benchmarks ===>")
    print("Cpu time := ", msmtDict["CpuTime"]/n_run)

# Pi_3
print("Non interactive protocol")
for k in [1, 2, 4, 8, 32]:
    scheme = PiNonInt(pairing_group, k)
    #pk, sk = scheme.setup()
    m = [i%2 for i in range(k)]

    credentials = [0 for i in range(n_run)]
    for i in range(n_run):
        credentials[i] = scheme.register()

    ec_group.StartBenchmark(["CpuTime"])
    for i in range(n_run):
        scheme.vote(credentials[i], m)
    ec_group.EndBenchmark()

    print(k)
    msmtDict = ec_group.GetGeneralBenchmarks()
    print("<=== General Benchmarks ===>")
    print("Cpu time := ", msmtDict["CpuTime"]/n_run)
