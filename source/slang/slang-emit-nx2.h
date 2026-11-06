#pragma once

#include "slang-ir.h"

namespace Slang
{
class DiagnosticSink;
class TargetProgram;

// Inline nonrecursive leaf calls while preserving their control flow.
bool inlineNX2LeafCalls(IRFunc* function, TargetProgram* targetProgram);

// Lower safely speculatable conditional values to IR select instructions.
bool lowerNX2SpeculatableConditionals(IRFunc* function);

// Remove loop regions without backedges and rebuild conditional join metadata.
bool lowerNX2AcyclicLoops(IRFunc* function);

// Lower supported NX2 matrix multiplication and transpose calls into ordinary IR.
bool lowerNX2MatrixOperations(IRFunc* entryPoint);

// Split mutable local structs into field storage before native emission.
bool lowerNX2LocalStructs(IRFunc* entryPoint);

SlangResult emitNX2Assembly(
    IRFunc* entryPoint,
    DiagnosticSink* sink,
    bool sceneTextureABI,
    StringBuilder* assembly);
} // namespace Slang