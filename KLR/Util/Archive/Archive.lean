/-
Copyright KLR Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

namespace KLR.Util.Archive

structure ArchiveEntry where
  filename : String
  content : ByteArray
  deriving Inhabited

instance : Repr ArchiveEntry where
  reprPrec e _ := repr e.filename

@[extern "lean_archive_create_tar"]
opaque createTar (entries : @&List ArchiveEntry) : ByteArray

@[extern "lean_archive_extract_tar"]
opaque extractTar (bytes : @&ByteArray) : List ArchiveEntry

end KLR.Util.Archive
