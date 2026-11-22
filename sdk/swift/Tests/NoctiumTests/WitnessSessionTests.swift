import Foundation
import Noctium
import XCTest
#if NOCTIUM_LOCALNET
import CryptoKit
#endif

final class WitnessSessionTests: XCTestCase {
    func testTypedWitnessAndCancellation() throws {
        let fixture = try XCTUnwrap(
            ProcessInfo.processInfo.environment["NOCTIUM_SWIFT_PLAN"],
            "Set NOCTIUM_SWIFT_PLAN to the compiled TypedWitness.scalarHost.control.json"
        )
        let plan = try decode(Data(contentsOf: URL(fileURLWithPath: fixture)))
        let attemptID = String(repeating: "b", count: 64)
        var fields = try beginFields(attemptID: attemptID)
        fields["plan"] = plan
        let begin = try encode(fields)
        let session = try WitnessSession(begin: begin)
        try complete(session, attemptID: attemptID)

        let cancelled = try WitnessSession(begin: begin)
        _ = try cancelled.advance()
        XCTAssertEqual(try decode(cancelled.cancel())["status"] as? String, "cancelled")
        XCTAssertThrowsError(try cancelled.privateRequest())
    }

    func testAuthenticatedWitnessProvesLocally() throws {
        guard let directory = ProcessInfo.processInfo.environment["NOCTIUM_SWIFT_PROOF_FIXTURE"] else {
            throw XCTSkip("Set NOCTIUM_SWIFT_PROOF_FIXTURE to the native proof fixture directory")
        }
        let root = URL(fileURLWithPath: directory, isDirectory: true)
        let proof = try prepareFixture(root: root, attemptID: String(repeating: "d", count: 64))
        let intent = try decode(proof.proveLocally())
        XCTAssertEqual(intent["status"] as? String, "proved")
        XCTAssertEqual(intent["funded"] as? Bool, false)
        XCTAssertEqual(intent["submitted"] as? Bool, false)
        XCTAssertFalse(try XCTUnwrap(intent["publicIntentHex"] as? String).isEmpty)
    }

#if NOCTIUM_LOCALNET
    func testOriginalPrivateClaimLocalnet() throws {
        guard let directory = ProcessInfo.processInfo.environment["NOCTIUM_SWIFT_PRIVATE_CLAIM_FIXTURE"] else {
            throw XCTSkip("Set NOCTIUM_SWIFT_PRIVATE_CLAIM_FIXTURE for the original private claim")
        }
        let root = URL(fileURLWithPath: directory, isDirectory: true)
        let id = freshAttempt()
        let namespace = "swift-claim-\(id.prefix(16))"
        var localnetConfig = try decode(Data(contentsOf: root.appendingPathComponent("localnet.json")))
        localnetConfig["journalDirectory"] = root.appendingPathComponent("journal-\(id)").path
        let localnet = try DevelopmentLocalnet(
            configuration: encode(localnetConfig), developmentSeed: Data(repeating: 0, count: 31) + Data([1])
        )
        let context = try decode(localnet.context())
        let blockTime = try XCTUnwrap(context["blockTime"] as? String)
        var options = try decode(Data(contentsOf: root.appendingPathComponent("proof.json")))
        options["ttl"] = try XCTUnwrap(UInt64(blockTime)) + 1800
        let proofDescriptor = try encode(options)
        let parameters = try Data(contentsOf: root.appendingPathComponent("srs"))
        let configuration = try Data(contentsOf: root.appendingPathComponent("runtime-config.json"))
        var invalid = try decode(configuration)
        var inputs = try XCTUnwrap(invalid["inputs"] as? [String: Any])
        XCTAssertNotEqual(inputs["secret"] as? String, "0")
        inputs["secret"] = "0"
        invalid["inputs"] = inputs
        XCTAssertThrowsError(try NativeProof(
            descriptor: proofDescriptor, configuration: encode(invalid), parameters: parameters
        )) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(1))
        }
        let proof = try NativeProof(
            descriptor: proofDescriptor, configuration: configuration, parameters: parameters
        )
        XCTAssertEqual(try decode(proof.proveLocally())["status"] as? String, "proved")
        let descriptor = try Data(contentsOf: root.appendingPathComponent("client.json"))
        let deployment = try proof.startDevelopmentDeployment(
            descriptor: descriptor, setup: developmentSetup(namespace: "\(namespace)-deploy")
        )
        let deployReceipt = try finalize(deployment, on: localnet)
        XCTAssertEqual(deployReceipt["event"] as? String, "Deploy")
        try deployment.close()

        let call = try proof.startDevelopmentCall(
            descriptor: descriptor, setup: developmentSetup(namespace: "\(namespace)-call")
        )
        let callReceipt = try finalize(call, on: localnet)
        XCTAssertEqual(callReceipt["event"] as? String, "Call")
        XCTAssertEqual(callReceipt["contractAddress"] as? String, deployReceipt["contractAddress"] as? String)
        let state = try call.finalizedState()
        let digest = SHA256.hash(data: state).map { String(format: "%02x", $0) }.joined()
        XCTAssertEqual(digest, "d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3")
        XCTAssertEqual(callReceipt["contractStateSha256"] as? String, digest)
        try call.close()

        let stateFile = "\(namespace).state"
        try state.write(to: root.appendingPathComponent(stateFile), options: .withoutOverwriting)
        let record = try encode(["deployment": deployReceipt, "call": callReceipt, "stateFile": stateFile])
        print("NOCTIUM_SWIFT_PRIVATE_CLAIM \(String(decoding: record, as: UTF8.self))")
    }

    func testDevelopmentTransactionRecoversTypedPrivateCommit() throws {
        guard let directory = ProcessInfo.processInfo.environment["NOCTIUM_SWIFT_LOCALNET_FIXTURE"] else {
            throw XCTSkip("Set NOCTIUM_SWIFT_LOCALNET_FIXTURE for an isolated development run")
        }
        let root = URL(fileURLWithPath: directory, isDirectory: true)
        var config = try decode(Data(contentsOf: root.appendingPathComponent("localnet.json")))
        let descriptor = try Data(contentsOf: root.appendingPathComponent("client.json"))
        let attemptID = freshAttempt()
        let namespace = "swift-witness-\(attemptID.prefix(16))"
        config["journalDirectory"] = root.appendingPathComponent("journal-\(attemptID)").path
        let localnet = try DevelopmentLocalnet(
            configuration: encode(config), developmentSeed: Data(repeating: 0, count: 31) + Data([1])
        )
        let chain = try decode(localnet.context())
        let chainTime = try XCTUnwrap(UInt64(try XCTUnwrap(chain["blockTime"] as? String)))
        let proof = try prepareFixture(
            root: root, attemptID: attemptID, namespace: namespace, revision: "r0", ttl: chainTime + 1800
        )
        XCTAssertEqual(try decode(proof.proveLocally())["status"] as? String, "proved")

        let deploy = try proof.startDevelopmentDeployment(
            descriptor: descriptor, setup: developmentSetup(namespace: "\(namespace)-deployment")
        )
        let initial = try deploy.send(.prepare)
        XCTAssertThrowsError(try deploy.close())
        try drive(deploy, on: localnet, from: initial)
        try drive(deploy, on: localnet, from: deploy.send(.submit))
        let deploymentReceipt = try observe(deploy, on: localnet)
        XCTAssertEqual(deploymentReceipt["event"] as? String, "Deploy")
        try drive(deploy, on: localnet, from: deploy.send(.commit))
        try deploy.close()

        let call = try proof.startDevelopmentCall(descriptor: descriptor)
        XCTAssertThrowsError(try proof.startDevelopmentCall(descriptor: descriptor))
        try drive(call, on: localnet, from: call.send(.prepare))
        let recovery = try call.recoveryContext()
        let sealed = try call.sealedTransaction()
        XCTAssertEqual(try localnet.privateValue(namespace: namespace, key: "cache/last"), Data("null".utf8))
        try drive(call, on: localnet, from: call.send(.submit))
        try call.close()

        for key in ["parameterCache", "parameterSource", "dustSrsSha256"] {
            config.removeValue(forKey: key)
        }
        let recoveryHost = try DevelopmentLocalnet(configuration: encode(config))
        let resumed = try DevelopmentTransaction.recover(descriptor: descriptor, context: recovery)
        try drive(resumed, on: recoveryHost, from: resumed.advance())
        XCTAssertEqual(try resumed.sealedTransaction(), sealed)
        let callReceipt = try observe(resumed, on: recoveryHost)
        XCTAssertEqual(callReceipt["event"] as? String, "Call")
        XCTAssertEqual(callReceipt["contractAddress"] as? String, deploymentReceipt["contractAddress"] as? String)
        let finalState = try resumed.finalizedState()
        let digest = SHA256.hash(data: finalState).map { String(format: "%02x", $0) }.joined()
        XCTAssertEqual(digest, "f9b24f4480110e62fe9333e5c3be687073922bd24b0935fbd62c0eb1b699c600")
        XCTAssertEqual(callReceipt["contractStateSha256"] as? String, digest)
        let committed = try drive(resumed, on: recoveryHost, from: resumed.send(.commit))
        XCTAssertEqual(committed["phase"] as? String, "Committed")
        XCTAssertEqual(committed["privateAcknowledged"] as? Bool, true)
        let saved = try decode(recoveryHost.privateValue(namespace: namespace, key: "cache/last"))
        XCTAssertEqual(saved["value"] as? String, "14")
        try resumed.close()
        let receipts = try encode(["deployment": deploymentReceipt, "call": callReceipt])
        print("NOCTIUM_SWIFT_RECEIPTS \(String(decoding: receipts, as: UTF8.self))")
    }

    @discardableResult
    private func drive(
        _ transaction: DevelopmentTransaction, on localnet: DevelopmentLocalnet, from initial: Data
    ) throws -> [String: Any] {
        var pending = initial
        for _ in 0..<128 {
            let step = try decode(pending)
            guard step["status"] as? String == "need_host" else {
                XCTAssertEqual(step["status"] as? String, "step_done", step["error"] as? String ?? "")
                return step
            }
            let sign = step["operation"] as? String == "approval.sign.v1"
            if sign {
                var crossed = step
                crossed["requestId"] = "1"
                XCTAssertThrowsError(try transaction.resolve(encode(crossed), using: localnet, approveSigning: true))
            }
            pending = try transaction.resolve(pending, using: localnet, approveSigning: sign)
        }
        throw WitnessSession.Failure.invalidResult
    }

    private func observe(_ transaction: DevelopmentTransaction, on localnet: DevelopmentLocalnet) throws -> [String: Any] {
        for _ in 0..<180 {
            let observed = try drive(transaction, on: localnet, from: transaction.send(.observe))
            if let receipt = observed["receipt"] as? [String: Any] { return receipt }
            Thread.sleep(forTimeInterval: 0.5)
        }
        throw WitnessSession.Failure.invalidResult
    }

    private func finalize(_ transaction: DevelopmentTransaction, on localnet: DevelopmentLocalnet) throws -> [String: Any] {
        try drive(transaction, on: localnet, from: transaction.send(.prepare))
        try drive(transaction, on: localnet, from: transaction.send(.submit))
        let receipt = try observe(transaction, on: localnet)
        XCTAssertEqual(try drive(transaction, on: localnet, from: transaction.send(.commit))["phase"] as? String, "Committed")
        return receipt
    }

    private func developmentSetup(namespace: String) throws -> Data {
        try encode([
            "hostContext": [
                "protocolVersion": 1, "namespace": namespace, "baseRevision": "r0",
                "attemptId": freshAttempt(), "operations": [], "providers": [],
                "commitCapability": "store",
                "capabilities": [["id": "store", "namespace": namespace, "keyPrefix": "fixture/",
                    "operations": ["private_state.stage.v1", "private_state.compare_exchange.v1"]]],
            ] as [String: Any],
            "stages": [],
        ])
    }

    private func freshAttempt() -> String {
        (UUID().uuidString + UUID().uuidString).replacingOccurrences(of: "-", with: "").lowercased()
    }
#endif

    private func prepareFixture(
        root: URL, attemptID: String, namespace: String = "noctium",
        revision: String = "fixture-r0", ttl: UInt64? = nil
    ) throws -> NativeProof {
        var descriptor = try decode(Data(contentsOf: root.appendingPathComponent("target.json")))
        if let ttl { descriptor["ttl"] = ttl }
        let targetDescriptor = try encode(descriptor)
        let bundle = try XCTUnwrap(descriptor["bundleDirectory"] as? String)
        let control = URL(fileURLWithPath: bundle).appendingPathComponent("witness/entrypoint.control.json")
        let plan = try Data(contentsOf: control)
        let parameters = try Data(contentsOf: root.appendingPathComponent("srs"))
        let begin = try encode(beginFields(attemptID: attemptID, namespace: namespace, revision: revision))
        let state = Data(#"{"state":{"total":"0"}}"#.utf8)
        var options = descriptor
        options.removeValue(forKey: "bundleDirectory")
        options["proofServiceCapability"] = "host.prover"
        options["maxResponseBytes"] = 1_048_576
        let proofDescriptor = try encode(options)

        XCTAssertThrowsError(try NativeWitness(
            targetDescriptor: targetDescriptor, initialState: state, parameters: parameters,
            plan: plan + Data([10]), begin: begin
        ))
        let target = try NativeWitness(
            targetDescriptor: targetDescriptor, initialState: state, parameters: parameters,
            plan: plan, begin: begin
        )
        XCTAssertEqual(try decode(target.targetInfo)["entrypoint"] as? String, "claim")
        XCTAssertThrowsError(try target.prepareProof(descriptor: proofDescriptor)) {
            XCTAssertEqual($0 as? WitnessSession.Failure, .nativeStatus(3))
        }
        try complete(target.session, attemptID: attemptID)
        let proof = try target.prepareProof(descriptor: proofDescriptor)
        XCTAssertThrowsError(try target.session.advance())
        XCTAssertThrowsError(try target.prepareProof(descriptor: proofDescriptor))
        return proof
    }

    private func beginFields(
        attemptID: String, namespace: String = "noctium", revision: String = "fixture-r0"
    ) throws -> [String: Any] {
        let context = try decode(Data("""
            {
              "protocolVersion":1,"namespace":"\(namespace)","baseRevision":"\(revision)",
              "attemptId":"\(attemptID)",
              "capabilities":[
                {"id":"private","namespace":"\(namespace)","keyPrefix":"cache/",
                 "operations":["private_state.read.v1","private_state.stage.v1","private_state.compare_exchange.v1"]},
                {"id":"lookup","namespace":"\(namespace)","keyPrefix":"lookup/","operations":["noctium.lookup.v1"]}
              ],
              "operations":[
                {"operation":"private_state.read.v1","argumentSchema":{"key":"Key"},"resultSchema":"UIntRange<256>"},
                {"operation":"noctium.lookup.v1","argumentSchema":{"seed":"UIntRange<256>"},"resultSchema":"UIntRange<256>"}
              ],
              "providers":[
                {"input":"cache","operation":"private_state.read.v1","capability":"private","arguments":{"key":"cache/last"}},
                {"input":"lookup","operation":"noctium.lookup.v1","capability":"lookup","arguments":{}}
              ],
              "commitCapability":"private","limits":{"requests":64,"writes":64,"privateBytes":65536}
            }
            """.utf8))
        return ["abiVersion": 1, "inputs": ["expected": "14", "seed": "7"], "hostContext": context]
    }

    private func complete(_ session: WitnessSession, attemptID: String) throws {
        var previousReply: Data?
        for (index, name) in ["cache", "cache", "lookup", "cache", "lookup"].enumerated() {
            let pending = try session.advance()
            let step = try decode(pending)
            XCTAssertEqual(step["status"] as? String, "need_host")
            let request = try XCTUnwrap(step["request"] as? [String: Any])
            XCTAssertEqual(request["name"] as? String, name)
            XCTAssertNil(request["invocationWrites"])
            let privateRequestBytes = try session.privateRequest()
            let privateRequest = try decode(privateRequestBytes)
            let writes = try XCTUnwrap(privateRequest["invocationWrites"] as? [String: [String: String]])
            XCTAssertEqual(writes["cache/last"]?["value"], "1")

            var reply = request.filter { ["requestId", "operation", "capability", "schema"].contains($0.key) }
            reply["protocolVersion"] = 2
            reply["attemptId"] = attemptID
            reply["outcome"] = "value"
            reply["value"] = name == "cache" ? "1" : "14"
            if index == 0 {
                let requestID = try XCTUnwrap(reply["requestId"] as? String)
                let mismatchedID = requestID == "999" ? "998" : "999"
                let rejectedReplies: [(String, String, Any)] = [
                    ("protocol version", "protocolVersion", 1),
                    ("mismatched request ID", "requestId", mismatchedID),
                    ("noncanonical request ID", "requestId", "0" + requestID),
                    ("attempt ID", "attemptId", String(repeating: "c", count: 64)),
                    ("operation", "operation", "noctium.other.v1"),
                    ("capability", "capability", "lookup"),
                    ("schema", "schema", "UIntRange<255>"),
                ]
                for (label, field, value) in rejectedReplies {
                    var invalid = reply
                    invalid[field] = value
                    XCTAssertThrowsError(
                        try session.resume(encode(invalid), typed: true), label
                    ) {
                        XCTAssertEqual(
                            $0 as? WitnessSession.Failure, .nativeStatus(4), label
                        )
                    }
                    XCTAssertEqual(try session.advance(), pending, label)
                    XCTAssertEqual(try session.privateRequest(), privateRequestBytes, label)
                }
            }
            if index == 1, let previousReply {
                XCTAssertThrowsError(
                    try session.resume(previousReply, typed: true), "stale replay"
                ) {
                    XCTAssertEqual(
                        $0 as? WitnessSession.Failure, .nativeStatus(4), "stale replay"
                    )
                }
                XCTAssertEqual(try session.advance(), pending, "stale replay")
                XCTAssertEqual(try session.privateRequest(), privateRequestBytes, "stale replay")
            }
            let validReply = try encode(reply)
            _ = try session.resume(validReply, typed: true)
            previousReply = validReply
        }
        let finished = try decode(session.advance())
        XCTAssertEqual(finished["status"] as? String, "completed")
        XCTAssertEqual(finished["result"] as? String, "14")
    }

    private func decode(_ bytes: Data) throws -> [String: Any] {
        try XCTUnwrap(JSONSerialization.jsonObject(with: bytes) as? [String: Any])
    }

    private func encode(_ value: [String: Any]) throws -> Data {
        try JSONSerialization.data(withJSONObject: value)
    }
}
