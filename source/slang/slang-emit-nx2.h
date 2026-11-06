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

// Lower supported NX2 matrix-vector intrinsic calls into scalar and vector IR.
bool lowerNX2MatrixVectorMul(IRFunc* entryPoint);

SlangResult emitNX2Assembly(
    IRFunc* entryPoint,
    DiagnosticSink* sink,
    bool sceneTextureABI,
    StringBuilder* assembly);
} // namespace Slang