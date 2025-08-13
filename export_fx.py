#!/usr/bin/env python3
"""
Enhanced script to analyze ATen operators in a PyTorch Transformer module
with detailed usage statistics and operator categorization.

"""

import os
import torch
import torch.nn as nn
from torch.export import export
from collections import defaultdict, Counter

class SimpleLinearModule(nn.Module):
    def __init__(self, in_features, out_features):
        super().__init__()
        self.linear = nn.Linear(in_features, out_features)
        
    def forward(self, x):
        return self.linear(x)

class SimpleAttentionModule(nn.Module):
    def forward(self, q, k, v):
        return nn.functional.scaled_dot_product_attention(q,k,v)

class SimpleTransformerModule(nn.Module):
    def __init__(self, d_model=512, nhead=8, num_layers=1):
        super().__init__()
        self.transformer = nn.Transformer(
            d_model=d_model,
            nhead=nhead,
            num_encoder_layers=num_layers,
            num_decoder_layers=num_layers,
            batch_first=True
        )
        
    def forward(self, src, tgt):
        return self.transformer(src, tgt)

def analyze_aten_operators(exported_program):
    aten_ops = []
    aten_op_counts = Counter()
    
    # Iterate through all nodes in the graph
    for node in exported_program.graph.nodes:
        if node.op == 'call_function':
            target_str = str(node.target)
            
            # Check if it's an ATen operator
            if 'aten.' in target_str:
                aten_ops.append(target_str)
                aten_op_counts[target_str] += 1
    
    return aten_ops, aten_op_counts

def do_export(model, example_args):
    return export(model, example_args).run_decompositions()

def print_report(aten_ops, aten_op_counts, exported_program):
    unique_ops = sorted(set(aten_ops))
    
    print(f"\nFound {len(unique_ops)} unique ATen operators:")
    print("=" * 60)
    
    for i, op in enumerate(unique_ops, 1):
        count = aten_op_counts[op]
        print(f"{i:2d}. {op:<40} (used {count} times)")
    
    # Summary statistics
    print(f"\nSummary Statistics:")
    print("=" * 60)
    print(f"Total ATen operator calls: {len(aten_ops)}")
    print(f"Unique ATen operators: {len(unique_ops)}")
    print(f"Most frequently used operator: {aten_op_counts.most_common(1)[0][0]} ({aten_op_counts.most_common(1)[0][1]} times)")
    
    # Graph structure
    total_nodes = len(list(exported_program.graph.nodes))
    aten_percentage = (len(aten_ops) / total_nodes) * 100
    print(f"ATen ops as % of total graph nodes: {aten_percentage:.1f}%")
    print()

def export_linear_model():
    model = SimpleLinearModule(in_features=10, out_features=5)
    model.eval()
    batch_size = 2
    input_tensor = torch.randn(batch_size, 10)
    return do_export(model, (input_tensor,))
def export_attention_model():
    model = SimpleAttentionModule()
    model.eval()
    batch_size = 2
    seq_len = 10
    embed_dim = 512
    q = torch.randn(batch_size, seq_len, embed_dim)
    k = torch.randn(batch_size, seq_len, embed_dim)
    v = torch.randn(batch_size, seq_len, embed_dim)
    return do_export(model, (q, k, v))
def export_transformer_model():
    model = SimpleTransformerModule(d_model=256, nhead=4, num_layers=1)
    model.eval()
    batch_size = 2
    seq_len = 10
    d_model = 256
    src = torch.randn(batch_size, seq_len, d_model)
    tgt = torch.randn(batch_size, seq_len, d_model)
    return do_export(model, (src, tgt))
def export_llama_model():
    from transformers import AutoModelForCausalLM, AutoTokenizer
    os.environ["TOKENIZERS_PARALLELISM"] = "false" # silence warnings when compiling

    ckpt = "meta-llama/Meta-Llama-3.1-8B-Instruct"
    ckpt = 'openlm-research/open_llama_3b_v2'
    model = AutoModelForCausalLM.from_pretrained(ckpt, torch_dtype=torch.float16)
    #tokenizer = AutoTokenizer.from_pretrained(ckpt)
    #prompt = "Why dogs are so cute?"
    #inputs = tokenizer(prompt, return_tensors="pt")
    inputs = (torch.tensor([[    1, 16644, 31844,   629,  3924,   322, 14138]]),)
    return do_export(model, inputs)

def main():
    program_exporters = [
        ("linear", export_linear_model),
        ("attention", export_attention_model),
        ("transformer", export_transformer_model),
        ("llama", export_llama_model),
    ]

    details = []
    for (name, exporter) in program_exporters:
        print(f"Exporting {name} model...")
        exported_program = exporter()
        aten_ops, aten_op_counts = analyze_aten_operators(exported_program)
        with open(f"fx/{name}_exported_program.fx", "w") as f:
            f.write(str(exported_program))
        details.append((name, aten_ops, aten_op_counts, exported_program))
    
    for (_, aten_ops, aten_op_counts, exported_program) in details:
        print_report(aten_ops, aten_op_counts, exported_program)

    all_ops = set()
    for _, aten_ops, _, _ in details:
        all_ops.update(aten_ops)

    all_ops = sorted(all_ops)

    op_table = defaultdict(list)
    for op in all_ops:
        for name, aten_ops, _, _ in details:
            op_table[op].append(op in aten_ops)

    print("\nOperator Usage Summary:")
    print("=" * 60)
    print(f"{'Operator':<40} {'Linear':<10} {'Attention':<10} {'Transformer':<10} {'Llama':<10}")
    print("-" * 60)
    for op in all_ops:
        usage = [str(op_table[op][i]) for i in range(len(program_exporters))]
        print(f"{op:<40} {' '.join(usage)}")
    print("=" * 60)
    print("End of report.")

    print("operator,linear,attention,transformer,llama")
    for op in all_ops:
        usage = ["X" if op_table[op][i] else "" for i in range(len(program_exporters))]
        print(f"{op},{','.join(usage)}")

if __name__ == "__main__":
    main()
