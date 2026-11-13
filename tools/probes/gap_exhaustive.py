import sys, itertools, time
sys.path.insert(0, '.')
import features as F

t0 = time.time()
print("n  max(g - ceil(delta))  witness              max(g - g2)  witness", flush=True)
for n in range(2, 13):
    wd = (-99, None); w2 = (-99, None)
    for bits in itertools.product('ab', repeat=n):
        s = ''.join(bits)
        g, lb, how = F.gamma_certified(s)
        if lb != g:            # unclosed bracket: skip, count separately
            continue
        f = F.features(s, want_packing=False, kmax=2)
        d = f['delta_ceil']; g2 = f['gamma2']
        if g - d > wd[0]: wd = (g - d, (s, g, d))
        if g - f['gamma2'] > w2[0]: w2 = (g - f['gamma2'], (s, g, f['gamma2']))
    print("%2d %6d  %-20s %6d  %-20s  [%.0fs]" % (n, wd[0], wd[1], w2[0], w2[1], time.time()-t0), flush=True)
