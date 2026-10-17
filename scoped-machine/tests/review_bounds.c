#include "net.h"
#include "lib.h"
#include "work.h"
#include <assert.h>

static void net_op(Net *net, NodeKind op, Payload p, NodeKind data, Payload q, NodeKind *kind, Payload *result) {
    int8_t minus = -1;
    NodeId root = net_node(net, A_ROOT, 1, &minus, (Payload){0});
    NodeId o = net_operation(net, op, p);
    net_connect(net, o, 1, root, 0);
    net_connect(net, o, 0, net_descriptor(net, data, q), 0);
    net_run(net);
    assert(net_root_read(net, root, kind, result));
}

static void mixed(size_t n) {
    assert(n >= 3 && n % 3 == 0);
    CaptureDecl *d = calloc(n, sizeof *d); Val *args = calloc(n, sizeof *args);
    RefId U = mk_universe(0), B = ref_var(declare_term(U, fc_true()));
    RefId b = ref_var(declare_term(B, fc_true())), body = 0, type = 0;
    FaceId guard = fc_true();
    for (size_t k = 0; k < n; k += 3) {
        DimVarId i = declare_dim(); FaceId f = fc_lit(i, 1); guard = fc_meet(guard, f);
        TermVarId X = declare_term(U, fc_true()), x = declare_term(ref_var(X), f);
        d[k] = (CaptureDecl){S_DIM, i, 0, LEVEL_NONE, fc_true()};
        d[k+1] = (CaptureDecl){S_TERM, X, U, 1, fc_true()};
        d[k+2] = (CaptureDecl){S_TERM, x, ref_var(X), 0, f};
        args[k] = (Val){VS_INTERVAL, iv_one()};
        args[k+1] = (Val){VS_REF, B}; args[k+2] = (Val){VS_REF, b};
        body = ref_var(x); type = ref_var(X);
    }
    ScopeId host = capture_scope(n, d, (Val){VS_REF,body}, type, 0, guard);
    const char *why = NULL; assert(scope_validate(host, &why));
    TypedPartial h = apply_scope(host, n, args); assert(h.body.id == b && h.type == B && h.guard == fc_true());
    Net net; net_init(&net); NodeKind kind; Payload r;
    net_op(&net, OP_CAPTURE_REF_SCOPE, (Payload){.a=net_capture_decls(n,d),.ref=type,.c=0,.face=guard}, D_REF, (Payload){.ref=body}, &kind, &r);
    assert(kind == D_SCOPE && r.a == host);
    net_op(&net, OP_APPLY_SCOPE, (Payload){.a=net_scope_args(n,args)}, D_SCOPE, (Payload){.a=host}, &kind, &r);
    assert(kind == D_TYPED_PARTIAL && r.ref == b && r.b == B && r.face == fc_true());
    net_op(&net, OP_CAPTURE_FACE_SCOPE, (Payload){.a=net_capture_decls(n,d)}, D_FACE, (Payload){.face=guard}, &kind, &r);
    assert(kind == D_SCOPE);
    net_op(&net, OP_APPLY_SCOPE, (Payload){.a=net_scope_args(n,args)}, D_SCOPE, r, &kind, &r);
    assert(kind == D_FACE && r.face == fc_true());
    net_free(&net); free(d); free(args);
    printf("mixed dependent telescope %zu: reference/face capture and application agree\n", n);
}

int main(int argc, char **argv) {
    assert(argc >= 2);
    const char *mode = argv[1];
    size_t n = argc > 2 ? strtoull(argv[2], NULL, 10) : 129;
    machine_init();
    if (!strcmp(mode, "bound-encoding")) {
        uint64_t a = bound_id(0, 0), b = bound_id(1u << 29, 0);
        printf("depth=0 id=%llu; depth=2^29 id=%llu; distinct=%d\n", (unsigned long long)a, (unsigned long long)b, a != b);
        machine_free(); return a == b;
    }
    if (!strcmp(mode, "mixed")) {
        mixed(n);
    } else if (!strcmp(mode, "sparse")) {
        Radix r; radix_init(&r); int values[5] = {1,2,3,4,5};
        size_t indices[5] = {0, 512, (size_t)1 << 26, (size_t)1 << 40, SIZE_MAX};
        for (size_t k = 0; k < 5; k++) *radix_slot(&r, indices[k], true) = &values[k];
        for (size_t k = 0; k < 5; k++) assert(radix_get(&r, indices[k]) == &values[k]);
        radix_free(&r, NULL, NULL); puts("sparse pointer directory covers SIZE_MAX without intervening allocation");
    } else if (!strcmp(mode, "cost")) {
        work_init();
        bool overflow = false;
        Cost sum = cost_add((1ULL << 62) - 1, 1, &overflow);
        printf("(2^62-1)+1 = %llu; resource_limit=%d\n", (unsigned long long)sum, overflow);
        work_free(); machine_free();
        return overflow || sum != (1ULL << 62);
    } else if (!strcmp(mode, "required")) {
        for (size_t k = 0; k < n; k++) term_require_push(fc_true());
        for (size_t k = 0; k < n; k++) term_require_pop();
        printf("required depth=%zu OK\n", n);
    } else if (!strcmp(mode, "levels")) {
        RefId u = mk_universe((1ULL << 32) + 1);
        assert(origin_payload(ref_origin(u)) == (1ULL << 32) + 1);
        puts("universe level=2^32+1 preserved");
    } else if (!strcmp(mode, "chunked")) {
        Chunked *c = malloc(sizeof *c); chunked_init(c, sizeof(uint64_t));
        size_t index = (size_t)1 << 26;
        *(uint64_t *)chunked_at(c, index) = 73;
        assert(*(uint64_t *)chunked_get(c, index) == 73);
        printf("sparse table index=%zu OK\n", index);
        chunked_free(c); free(c);
    } else if (!strcmp(mode, "signature")) {
        RefId U = mk_universe(0), A = ref_var(declare_term(U, fc_true()));
        RefId x = ref_var(declare_term(A, fc_true())), t = mk_refl(0, A, x);
        size_t count = tnode_signature(t, NULL, 0);
        assert(count > 0); ParamSig *sig = malloc(count * sizeof *sig);
        assert(tnode_signature(t, sig, count) == count);
        printf("complete signature: %zu entries\n", count); free(sig);
    } else if (!strcmp(mode, "template-width")) {
        templates_init();
        size_t max_nf = 0; TNodeId max_q = 0;
        for (TNodeId q = 1; q <= interner_count(&M.tnodes); q++) {
            TNodeSide *s = chunked_get(&M.tnode_side, q - 1);
            size_t nf; interner_get(&M.keys, s->free_slots, &nf);
            if (nf > max_nf) { max_nf = nf; max_q = q; }
        }
        printf("registered template max retained slots=%zu node=%llu definition=%s\n", max_nf, (unsigned long long)max_q, tdef_name(tnode_def(max_q)));
    } else {
        assert(n > 0);
        CaptureDecl *d = calloc(n, sizeof *d);
        Val *args = calloc(n, sizeof *args);
        uint64_t *atoms = malloc(n * sizeof *atoms);
        for (size_t k = 0; k < n; k++) {
            DimVarId i = declare_dim();
            d[k] = (CaptureDecl){S_DIM, i, 0, LEVEL_NONE, fc_true()};
            atoms[k] = IV_ATOM(i, false);
            args[k] = (Val){VS_INTERVAL, iv_one()};
        }
        Dnf dn; dnf_init(&dn); dnf_add_clause(&dn, atoms, n);
        IntervalId r = iv_from_dnf(&dn); dnf_free(&dn);
        Words ds; words_init(&ds); iv_dims(r, &ds); assert(ds.n == n); words_free(&ds);
        if (!strcmp(mode, "interval")) {
            MapBuilder m; mapb_init(&m);
            for (size_t k = 0; k < n; k++) mapb_dim(&m, d[k].id, iv_one());
            assert(iv_reindex(r, mapb_finish(&m)) == iv_one());
            FaceId f = fc_endpoint(r, 1);
            for (size_t k = 0; k < n; k++) assert(fc_entails(f, fc_lit(d[k].id, 1)));
            assert(fc_is_false(fc_forall(d[n-1].id, f)));
            printf("%zu distinct dimensions: DNF, substitution, entailment, forall OK\n", n);
        } else {
            ScopeId s = capture_scope(n, d, (Val){VS_INTERVAL, r}, 0, LEVEL_NONE, fc_true());
            const char *why = NULL; assert(scope_validate(s, &why));
            assert(apply_scope(s, n, args).body.id == iv_one());
            if (!strcmp(mode, "scope")) printf("host scope capture/apply %zu OK\n", n);
            else {
                Net net; net_init(&net); NodeKind kind; Payload result;
                if (!strcmp(mode, "net-capture")) {
                    net_op(&net, OP_CAPTURE_INTERVAL_SCOPE, (Payload){.a=net_capture_decls(n,d)}, D_INTERVAL, (Payload){.a=r}, &kind, &result);
                    assert(kind == D_SCOPE && result.a == s);
                } else if (!strcmp(mode, "net-apply")) {
                    net_op(&net, OP_APPLY_SCOPE, (Payload){.a=net_scope_args(n,args)}, D_SCOPE, (Payload){.a=s}, &kind, &result);
                    assert(kind == D_INTERVAL && result.a == iv_one());
                } else assert(!"unknown mode");
                printf("%s %zu agrees with host operation\n", mode, n);
                net_free(&net);
            }
        }
        free(d); free(args); free(atoms);
    }
    machine_free();
    return 0;
}
