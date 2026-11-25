// swift-tools-version: 6.0
import PackageDescription

let localnet = false
let features: [SwiftSetting] = localnet ? [.define("NOCTIUM_LOCALNET")] : []

let package = Package(
    name: "Noctium",
    platforms: [.iOS(.v16), .macOS(.v13)],
    products: [.library(name: "Noctium", targets: ["Noctium"])],
    targets: [
        .binaryTarget(name: "CNoctium", path: "CNoctium.xcframework"),
        .target(
            name: "Noctium",
            dependencies: ["CNoctium"],
            swiftSettings: features,
            linkerSettings: [
                .linkedFramework("Security"),
                .linkedFramework("SystemConfiguration", .when(platforms: [.macOS])),
                .linkedFramework("IOKit", .when(platforms: [.macOS])),
            ]
        ),
        .testTarget(
            name: "NoctiumTests",
            dependencies: ["Noctium"],
            resources: [.copy("Fixtures")],
            swiftSettings: features
        ),
    ]
)
