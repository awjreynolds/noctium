import CNoctium
import Foundation

public enum LedgerSnapshot {
    public static func collectionPage(request: Data, plan: Data, snapshot: Data) throws -> Data {
        var token: UInt64 = 0
        let status = request.withBytePointer { requestBytes, requestSize in
            plan.withBytePointer { planBytes, planSize in
                snapshot.withBytePointer { snapshotBytes, snapshotSize in
                    noctium_ledger_collection_page(
                        requestBytes, requestSize,
                        planBytes, planSize,
                        snapshotBytes, snapshotSize,
                        &token
                    )
                }
            }
        }
        try WitnessSession.check(status)
        return try takeNativeResult(token)
    }
}
