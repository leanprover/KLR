# KLR On-Disk Format

KLR uses [CBOR](https://cbor.io) as its on-disk format.

The exact details are stull in flux.

## Assignment of tags

| Lean Type | Type Tag |
|-|-|
| Internal ASTs | 1 - 99 |
| Core.* | 100 - 149 |
| Core.Operators.* | 150 - 234 |
| KLRMetaData | 235 (0xeb) |
| Contents | 236 (0xec) |
| Option | 255 (0xff) |
