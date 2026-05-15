#!/usr/bin/env python3
import json

from Crypto.PublicKey import ECC
from fpylll import IntegerMatrix, LLL
from pwn import context, remote
from sympy import Matrix, Poly, eye, symbols, zeros
from py_ecc.bls.ciphersuites import G2ProofOfPossession as bls
from py_ecc.bls.g2_primitives import G1_to_pubkey, pubkey_to_G1
from py_ecc.optimized_bls12_381.optimized_curve import G1, add, curve_order, neg, multiply


HOST = "154.57.164.70"
PORT = 30893
context.log_level = "error"

P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
P256_B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
P256_GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
P256_GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
LOW_BITS = 32


def recv_json(io):
    line = io.recvline()
    while line and not line.strip():
        line = io.recvline()
    return json.loads(line)


def cmd(io, obj):
    io.sendlineafter(b"> ", json.dumps(obj).encode())
    return recv_json(io)


def lll_rows(matrix):
    rows = [[int(matrix[i, j]) for j in range(matrix.cols)] for i in range(matrix.rows)]
    im = IntegerMatrix.from_matrix(rows)
    LLL.reduction(im)
    return [[int(im[i, j]) for j in range(im.ncols)] for i in range(im.nrows)]


def is_p256_point(x, y):
    return (y * y - x * x * x + 3 * x - P256_B) % P256_P == 0


def recover_rng_point(outputs):
    xs = [v << LOW_BITS for v in outputs]
    a1, b1, a2, b2, a3, b3 = symbols("a1 b1 a2 b2 a3 b3")
    x1, y1, x2, y2, x3, y3 = xs

    polys = [
        (y1 + b1) ** 2 - (x1 + a1) ** 3 + 3 * (x1 + a1) - P256_B,
        (y2 + b2) ** 2 - (x2 + a2) ** 3 + 3 * (x2 + a2) - P256_B,
        (y3 + b3) ** 2 - (x3 + a3) ** 3 + 3 * (x3 + a3) - P256_B,
        (x2 + a2) * ((x1 + a1) - P256_GX) ** 2
        - ((y1 + b1) - P256_GY) ** 2
        + (x1 + a1) * ((x1 + a1) - P256_GX) ** 2
        + P256_GX * ((x1 + a1) - P256_GX) ** 2,
        (y2 + b2) * ((x1 + a1) - P256_GX)
        - ((y1 + b1) - P256_GY) * ((x1 + a1) - (x2 + a2))
        + (y1 + b1) * ((x1 + a1) - P256_GX),
        (x3 + a3) * ((x2 + a2) - P256_GX) ** 2
        - ((y2 + b2) - P256_GY) ** 2
        + (x2 + a2) * ((x2 + a2) - P256_GX) ** 2
        + P256_GX * ((x2 + a2) - P256_GX) ** 2,
        (y3 + b3) * ((x2 + a2) - P256_GX)
        - ((y2 + b2) - P256_GY) * ((x2 + a2) - (x3 + a3))
        + (y2 + b2) * ((x2 + a2) - P256_GX),
    ]

    variables = (a1, b1, a2, b2, a3, b3)
    monomials = []
    coefficient_rows = []
    for expr in polys:
        poly = Poly(expr, *variables, modulus=P256_P)
        coeffs = {m: int(c) % P256_P for m, c in zip(poly.monoms(), poly.coeffs())}
        coefficient_rows.append(coeffs)
        for monomial in coeffs:
            if monomial not in monomials:
                monomials.append(monomial)

    constant = (0, 0, 0, 0, 0, 0)
    monomials = [m for m in monomials if m != constant] + [constant]
    matrix = Matrix([[row.get(m, 0) for m in monomials] for row in coefficient_rows])
    rows, cols = matrix.rows, matrix.cols
    lattice = (eye(rows) * P256_P).row_join(matrix).col_join(zeros(cols, rows).row_join(eye(cols)))
    lattice[rows + monomials.index(constant), rows + monomials.index(constant)] = 2**256

    unit_indices = []
    for idx in range(6):
        unit = [0] * 6
        unit[idx] = 1
        unit_indices.append(monomials.index(tuple(unit)))

    for row in lll_rows(lattice.T):
        coeffs = row[rows:]
        for sign in (1, -1):
            lows = [sign * coeffs[i] for i in unit_indices]
            if not all(0 <= v < 2**LOW_BITS for v in lows):
                continue
            points = [
                (xs[0] + lows[0], xs[1] + lows[1]),
                (xs[2] + lows[2], xs[3] + lows[3]),
                (xs[4] + lows[4], xs[5] + lows[5]),
            ]
            if not all(is_p256_point(*point) for point in points):
                continue
            try:
                g = ECC.EccPoint(P256_GX, P256_GY, curve="p256")
                p1_next = ECC.EccPoint(*points[0], curve="p256") + g
                p2_next = ECC.EccPoint(*points[1], curve="p256") + g
                if (
                    points[1] == (int(p1_next.x), int(p1_next.y))
                    and points[2] == (int(p2_next.x), int(p2_next.y))
                ):
                    return ECC.EccPoint(*points[2], curve="p256")
            except ValueError:
                pass

    raise RuntimeError("failed to recover RNG point")


def predict_challenge_bits(outputs):
    point = recover_rng_point(outputs)
    g = ECC.EccPoint(P256_GX, P256_GY, curve="p256")
    bits = []
    while len(bits) < 64:
        point += g
        bits.append((int(point.x) >> LOW_BITS) & 1)
        bits.append((int(point.y) >> LOW_BITS) & 1)
    return bits[:64]


def main():
    io = remote(HOST, PORT)
    io.recvuntil(b"}\n\n")
    print("[*] connected")

    created = cmd(io, {"cmd": "create"})
    print("[*] created robot")
    sk = int(created["sk"], 16)
    robot_id = created["robot_id"]

    list_sig = bls.Sign(sk, b"list").hex()
    robots = cmd(io, {"cmd": "list", "robot_id": robot_id, "sig": list_sig})
    print(f"[*] listed {len(robots)} robots")

    aggregate = None
    for robot in robots:
        point = pubkey_to_G1(bytes.fromhex(robot["pk"]))
        aggregate = point if aggregate is None else add(aggregate, point)

    target_pk = multiply(G1, sk)
    rogue_pk = add(target_pk, neg(aggregate))
    rogue_pk_hex = G1_to_pubkey(rogue_pk).hex()

    joined = cmd(io, {"cmd": "join", "pk": rogue_pk_hex})
    print("[*] joined rogue robot")
    rogue_id = joined["robot_id"]
    rng_outputs = [int(robot["robot_id"], 16) for robot in robots] + [int(rogue_id, 16)]
    challenge_bits = predict_challenge_bits(rng_outputs)
    print("[*] predicted proof branches")

    io.sendlineafter(b"> ", json.dumps({"cmd": "verify", "robot_id": rogue_id}).encode())
    proof_msg = recv_json(io)
    print(f"[*] verify says: {proof_msg}")

    known_x = 1337
    known_sk_x = 0xB1055ED
    c_for_x = G1_to_pubkey(multiply(G1, known_x)).hex()
    c_for_sk_x = G1_to_pubkey(add(multiply(G1, known_sk_x), neg(rogue_pk))).hex()

    for bit in challenge_bits:
        c_hex = c_for_x if bit else c_for_sk_x
        io.sendlineafter(b"(hex): ", c_hex.encode())
        prompt = io.recvuntil(b": ")
        if b"Give me x" in prompt:
            io.sendline(hex(known_x).encode())
        else:
            io.sendline(hex(known_sk_x).encode())
    print("[*] proof responses sent")

    print(recv_json(io))

    unveil_sig = bls.Sign(sk, b"unveil_secrets").hex()
    print(cmd(io, {"cmd": "unveil_secrets", "sig": unveil_sig}))


if __name__ == "__main__":
    main()
