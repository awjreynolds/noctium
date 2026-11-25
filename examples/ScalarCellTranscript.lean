import Noctium.Frontend

open scoped Noctium

noctium_circuit scalarCellTranscriptInput where
  public delta : UInt 8
end

noctium_contract ScalarCellTranscript where
  cell total : UInt 16
  entry apply uses scalarCellTranscriptInput where
    read total as before
    write total := cast(UInt 16, add(before, delta))
    read total as after
    return observed : UInt 16 := after
  end
end
