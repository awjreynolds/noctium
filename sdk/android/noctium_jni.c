#include <jni.h>
#include <stdbool.h>
#include "noctium_control.h"
#include "noctium_native.h"

enum { CONTROL_BYTES = 1024 * 1024, DESCRIPTOR_BYTES = 64 * 1024, SRS_BYTES = 128 * 1024 * 1024 };

static void fail(JNIEnv *env, int32_t status) {
    if ((*env)->ExceptionCheck(env)) return;
    jclass type = (*env)->FindClass(env, "org/noctium/sdk/NoctiumFailure");
    if (!type) return;
    jmethodID init = (*env)->GetMethodID(env, type, "<init>", "(I)V");
    if (!init) return;
    jobject error = (*env)->NewObject(env, type, init, (jint)status);
    if (error) (*env)->Throw(env, error);
}

static jbyte *borrow_input(JNIEnv *env, jbyteArray input, jsize *length, jsize limit) {
    *length = input ? (*env)->GetArrayLength(env, input) : 0;
    if (*length <= 0 || *length > limit) {
        fail(env, *length <= 0 ? NOCTIUM_CONTROL_INVALID_ARGUMENT : NOCTIUM_CONTROL_LIMIT);
        return NULL;
    }
    jbyte *bytes = (*env)->GetByteArrayElements(env, input, NULL);
    if (!bytes) fail(env, NOCTIUM_CONTROL_INTERNAL);
    return bytes;
}

typedef struct {
    jbyteArray array;
    jsize limit;
    jsize length;
    jbyte *bytes;
} Input;

static void release_inputs(JNIEnv *env, Input inputs[], size_t count) {
    for (size_t i = 0; i < count; ++i) {
        (*env)->ReleaseByteArrayElements(env, inputs[i].array, inputs[i].bytes, JNI_ABORT);
    }
}

static bool borrow_inputs(JNIEnv *env, Input inputs[], size_t count) {
    for (size_t i = 0; i < count; ++i) {
        Input *input = &inputs[i];
        input->bytes = borrow_input(env, input->array, &input->length, input->limit);
        if (!input->bytes) {
            release_inputs(env, inputs, i);
            return false;
        }
    }
    return true;
}

typedef struct {
    int32_t (*length)(uint64_t, size_t *);
    int32_t (*copy)(uint64_t, uint8_t *, size_t, size_t *);
    int32_t (*release)(uint64_t);
} ResultAccess;

static const ResultAccess control_result = {
    noctium_control_result_length, noctium_control_result_copy, noctium_control_result_free
};
static const ResultAccess control_private = {
    noctium_control_private_length, noctium_control_private_copy, noctium_control_private_free
};
static const ResultAccess native_result = {
    noctium_native_result_length, noctium_native_result_copy, noctium_native_result_free
};

static jbyteArray take_result(JNIEnv *env, uint64_t token, const ResultAccess *access) {
    jbyteArray result = NULL;
    size_t size = 0;
    int32_t status = access->length(token, &size);
    if (status == NOCTIUM_CONTROL_OK) {
        if (size == 0 || size > INT32_MAX) {
            status = NOCTIUM_CONTROL_INTERNAL;
        } else {
            result = (*env)->NewByteArray(env, (jsize)size);
            jbyte *data = result ? (*env)->GetByteArrayElements(env, result, NULL) : NULL;
            if (data) {
                size_t written = 0;
                status = access->copy(token, (uint8_t *)data, size, &written);
                if (status == NOCTIUM_CONTROL_OK && written != size)
                    status = NOCTIUM_CONTROL_INTERNAL;
                (*env)->ReleaseByteArrayElements(env, result, data,
                    status == NOCTIUM_CONTROL_OK ? 0 : JNI_ABORT);
            } else {
                status = NOCTIUM_CONTROL_INTERNAL;
            }
        }
    }
    access->release(token);
    if (status != NOCTIUM_CONTROL_OK) {
        fail(env, status);
        return NULL;
    }
    return result;
}

static jbyteArray step(JNIEnv *env, jlong handle,
        int32_t (*operation)(uint64_t, uint64_t *), const ResultAccess *access) {
    uint64_t token = 0;
    int32_t status = operation((uint64_t)handle, &token);
    if (status != NOCTIUM_CONTROL_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, token, access);
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_Native_open(
        JNIEnv *env, jobject self, jbyteArray input) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, input, &length, CONTROL_BYTES);
    if (!bytes) return 0;
    uint64_t handle = 0;
    int32_t status = noctium_control_begin((const uint8_t *)bytes, (size_t)length, &handle);
    (*env)->ReleaseByteArrayElements(env, input, bytes, JNI_ABORT);
    if (status != NOCTIUM_CONTROL_OK) fail(env, status);
    return (jlong)handle;
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_advance(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    return step(env, handle, noctium_control_advance, &control_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_resume(
        JNIEnv *env, jobject self, jlong handle, jbyteArray response, jboolean typed) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, response, &length, CONTROL_BYTES);
    if (!bytes) return NULL;
    uint64_t token = 0;
    int32_t (*resume)(uint64_t, const uint8_t *, size_t, uint64_t *) =
        typed ? noctium_control_resume_typed : noctium_control_resume;
    int32_t status = resume((uint64_t)handle, (const uint8_t *)bytes, (size_t)length, &token);
    (*env)->ReleaseByteArrayElements(env, response, bytes, JNI_ABORT);
    if (status != NOCTIUM_CONTROL_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, token, &control_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_privateRequest(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    return step(env, handle, noctium_control_private_request, &control_private);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_cancel(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    return step(env, handle, noctium_control_cancel, &control_result);
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_Native_close(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    int32_t status = noctium_control_free((uint64_t)handle);
    if (status != NOCTIUM_CONTROL_OK) fail(env, status);
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_Native_targetOpen(
        JNIEnv *env, jobject self, jbyteArray descriptor, jbyteArray state, jbyteArray srs, jbyteArray entropy) {
    (void)self;
    Input inputs[] = {
        {.array = descriptor, .limit = DESCRIPTOR_BYTES},
        {.array = state, .limit = CONTROL_BYTES},
        {.array = srs, .limit = SRS_BYTES},
        {.array = entropy, .limit = 32},
    };
    if (!borrow_inputs(env, inputs, 4)) return 0;
    uint64_t target = 0, result = 0;
    int32_t status = noctium_native_witness_target_begin(
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length,
        (const uint8_t *)inputs[2].bytes, (size_t)inputs[2].length,
        (const uint8_t *)inputs[3].bytes, (size_t)inputs[3].length,
        &target, &result);
    release_inputs(env, inputs, 4);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    else noctium_native_result_free(result);
    return (jlong)target;
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_Native_targetWitness(
        JNIEnv *env, jobject self, jlong target, jbyteArray plan, jbyteArray begin) {
    (void)self;
    Input inputs[] = {{.array = plan, .limit = CONTROL_BYTES}, {.array = begin, .limit = CONTROL_BYTES}};
    if (!borrow_inputs(env, inputs, 2)) return 0;
    uint64_t control = 0;
    int32_t status = noctium_control_begin_from_native_target((uint64_t)target,
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length, &control);
    release_inputs(env, inputs, 2);
    if (status != NOCTIUM_CONTROL_OK) fail(env, status);
    return (jlong)control;
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_Native_targetClose(JNIEnv *env, jobject self, jlong target) {
    (void)self;
    int32_t status = noctium_native_target_context_free((uint64_t)target);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_Native_proofPrepare(
        JNIEnv *env, jobject self, jlong target, jlong witness, jbyteArray descriptor,
        jbyteArray srs, jbyteArray entropy) {
    (void)self;
    Input inputs[] = {
        {.array = descriptor, .limit = DESCRIPTOR_BYTES},
        {.array = srs, .limit = SRS_BYTES},
        {.array = entropy, .limit = 32},
    };
    if (!borrow_inputs(env, inputs, 3)) return 0;
    uint64_t proof = 0;
    int32_t status = noctium_native_begin_from_witness(
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length, (uint64_t)target, (uint64_t)witness,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length,
        (const uint8_t *)inputs[2].bytes, (size_t)inputs[2].length, &proof);
    release_inputs(env, inputs, 3);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    return (jlong)proof;
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_proofAdvance(
        JNIEnv *env, jobject self, jlong proof) {
    (void)self;
    return step(env, proof, noctium_native_advance, &native_result);
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_Native_proofOpen(
        JNIEnv *env, jobject self, jbyteArray descriptor, jbyteArray configuration,
        jbyteArray srs, jbyteArray entropy) {
    (void)self;
    Input inputs[] = {
        {.array = descriptor, .limit = DESCRIPTOR_BYTES},
        {.array = configuration, .limit = CONTROL_BYTES},
        {.array = srs, .limit = SRS_BYTES},
        {.array = entropy, .limit = 32},
    };
    if (!borrow_inputs(env, inputs, 4)) return 0;
    uint64_t proof = 0;
    int32_t status = noctium_native_begin(
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length,
        (const uint8_t *)inputs[2].bytes, (size_t)inputs[2].length,
        (const uint8_t *)inputs[3].bytes, (size_t)inputs[3].length, &proof);
    release_inputs(env, inputs, 4);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    return (jlong)proof;
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_proofGenerate(
        JNIEnv *env, jobject self, jlong proof, jbyteArray entropy) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, entropy, &length, 32);
    if (!bytes) return NULL;
    uint64_t payload = 0, result = 0;
    int32_t status = noctium_native_private_request((uint64_t)proof, &payload);
    if (status == NOCTIUM_NATIVE_OK) {
        status = noctium_native_local_prove(payload, (const uint8_t *)bytes, (size_t)length, &result);
        noctium_native_private_free(payload);
    }
    (*env)->ReleaseByteArrayElements(env, entropy, bytes, JNI_ABORT);
    if (status != NOCTIUM_NATIVE_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, result, &native_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_proofAttach(
        JNIEnv *env, jobject self, jlong proof, jbyteArray metadata, jbyteArray response) {
    (void)self;
    Input inputs[] = {
        {.array = metadata, .limit = DESCRIPTOR_BYTES},
        {.array = response, .limit = CONTROL_BYTES},
    };
    if (!borrow_inputs(env, inputs, 2)) return NULL;
    uint64_t result = 0;
    int32_t status = noctium_native_resume((uint64_t)proof,
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length, &result);
    release_inputs(env, inputs, 2);
    if (status != NOCTIUM_NATIVE_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, result, &native_result);
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_Native_proofCancel(JNIEnv *env, jobject self, jlong proof) {
    (void)self;
    int32_t status = noctium_native_cancel((uint64_t)proof);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_Native_proofClose(JNIEnv *env, jobject self, jlong proof) {
    (void)self;
    int32_t status = noctium_native_free((uint64_t)proof);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_collectionPage(
        JNIEnv *env, jobject self, jbyteArray request, jbyteArray plan, jbyteArray snapshot) {
    (void)self;
    Input inputs[] = {
        {.array = request, .limit = 64 * 1024},
        {.array = plan, .limit = CONTROL_BYTES},
        {.array = snapshot, .limit = CONTROL_BYTES},
    };
    if (!borrow_inputs(env, inputs, 3)) return NULL;
    uint64_t result = 0;
    int32_t status = noctium_ledger_collection_page(
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length,
        (const uint8_t *)inputs[2].bytes, (size_t)inputs[2].length, &result);
    release_inputs(env, inputs, 3);
    if (status != NOCTIUM_NATIVE_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, result, &native_result);
}

#ifdef NOCTIUM_LOCALNET
enum { RECOVERY_CONTEXT_BYTES = 1200000 };

static const ResultAccess native_private = {
    noctium_native_private_length, noctium_native_private_copy, noctium_native_private_free
};

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_LocalnetBridge_open(
        JNIEnv *env, jobject self, jbyteArray configuration, jbyteArray development_seed) {
    (void)self;
    Input inputs[] = {
        {.array = configuration, .limit = DESCRIPTOR_BYTES},
        {.array = development_seed, .limit = 32},
    };
    size_t count = !development_seed || (*env)->GetArrayLength(env, development_seed) == 0 ? 1 : 2;
    if (!borrow_inputs(env, inputs, count)) return 0;
    uint64_t adapter = 0;
    int32_t status = noctium_localnet_open(
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length, &adapter);
    release_inputs(env, inputs, count);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    return (jlong)adapter;
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_context(
        JNIEnv *env, jobject self, jlong adapter) {
    (void)self;
    return step(env, adapter, noctium_localnet_context, &native_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_privateValue(
        JNIEnv *env, jobject self, jlong adapter, jbyteArray query) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, query, &length, DESCRIPTOR_BYTES);
    if (!bytes) return NULL;
    uint64_t result = 0;
    int32_t status = noctium_localnet_private_value((uint64_t)adapter,
        (const uint8_t *)bytes, (size_t)length, &result);
    (*env)->ReleaseByteArrayElements(env, query, bytes, JNI_ABORT);
    if (status != NOCTIUM_NATIVE_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, result, &native_private);
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_LocalnetBridge_close(
        JNIEnv *env, jobject self, jlong adapter) {
    (void)self;
    int32_t status = noctium_localnet_free((uint64_t)adapter);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_LocalnetBridge_start(
        JNIEnv *env, jobject self, jlong proof, jint kind, jbyteArray descriptor, jbyteArray setup) {
    (void)self;
    Input inputs[] = {{.array = descriptor, .limit = DESCRIPTOR_BYTES}, {.array = setup, .limit = CONTROL_BYTES}};
    if (!borrow_inputs(env, inputs, 2)) return 0;
    uint64_t client = 0;
    int32_t status = noctium_client_start((uint64_t)proof, (uint32_t)kind,
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length, &client);
    release_inputs(env, inputs, 2);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    return (jlong)client;
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_LocalnetBridge_startFromWitness(
        JNIEnv *env, jobject self, jlong proof, jbyteArray descriptor) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, descriptor, &length, DESCRIPTOR_BYTES);
    if (!bytes) return 0;
    uint64_t client = 0;
    int32_t status = noctium_client_start_from_witness((uint64_t)proof,
        (const uint8_t *)bytes, (size_t)length, &client);
    (*env)->ReleaseByteArrayElements(env, descriptor, bytes, JNI_ABORT);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    return (jlong)client;
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_LocalnetBridge_recover(
        JNIEnv *env, jobject self, jbyteArray descriptor, jbyteArray context) {
    (void)self;
    Input inputs[] = {
        {.array = descriptor, .limit = DESCRIPTOR_BYTES},
        {.array = context, .limit = RECOVERY_CONTEXT_BYTES},
    };
    if (!borrow_inputs(env, inputs, 2)) return 0;
    uint64_t client = 0;
    int32_t status = noctium_client_recover(
        (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length,
        (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length, &client);
    release_inputs(env, inputs, 2);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
    return (jlong)client;
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_command(
        JNIEnv *env, jobject self, jlong client, jbyteArray command) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, command, &length, 16);
    if (!bytes) return NULL;
    uint64_t result = 0;
    int32_t status = noctium_client_command((uint64_t)client,
        (const uint8_t *)bytes, (size_t)length, &result);
    (*env)->ReleaseByteArrayElements(env, command, bytes, JNI_ABORT);
    if (status != NOCTIUM_NATIVE_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, result, &native_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_resolve(
        JNIEnv *env, jobject self, jlong client, jlong adapter, jboolean approve, jbyteArray metadata,
        jbyteArray entropy) {
    (void)self;
    Input inputs[] = {{.array = metadata, .limit = DESCRIPTOR_BYTES}, {.array = entropy, .limit = 32}};
    size_t count = entropy == NULL ? 1 : 2;
    if (!borrow_inputs(env, inputs, count)) return NULL;
    uint64_t request = 0, reply = 0, result = 0;
    int32_t status = noctium_client_request((uint64_t)client, &request);
    if (status == NOCTIUM_NATIVE_OK) {
        status = adapter ? noctium_localnet_resolve((uint64_t)adapter, request, approve ? 1 : 0,
            (const uint8_t *)inputs[1].bytes, (size_t)inputs[1].length, &reply) :
            noctium_client_service_failure(request, &reply);
        noctium_client_service_free(request);
        if (status == NOCTIUM_NATIVE_OK) {
            status = noctium_client_resume((uint64_t)client,
                (const uint8_t *)inputs[0].bytes, (size_t)inputs[0].length, reply, &result);
            noctium_client_service_free(reply);
        }
    }
    release_inputs(env, inputs, count);
    if (status != NOCTIUM_NATIVE_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, result, &native_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_advance(
        JNIEnv *env, jobject self, jlong client) {
    (void)self;
    return step(env, client, noctium_client_advance, &native_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_recoveryContext(
        JNIEnv *env, jobject self, jlong client) {
    (void)self;
    return step(env, client, noctium_client_recovery_context, &native_private);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_finalizedState(
        JNIEnv *env, jobject self, jlong client) {
    (void)self;
    return step(env, client, noctium_client_receipt_state, &native_result);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_LocalnetBridge_sealedTransaction(
        JNIEnv *env, jobject self, jlong client) {
    (void)self;
    return step(env, client, noctium_client_transaction, &native_result);
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_LocalnetBridge_detach(
        JNIEnv *env, jobject self, jlong client) {
    (void)self;
    int32_t status = noctium_client_detach((uint64_t)client);
    if (status != NOCTIUM_NATIVE_OK) fail(env, status);
}
#endif
