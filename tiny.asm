; https://www.muppetlabs.com/~breadbox/software/tiny/somewhat.html

  ; tiny.asm
  
  BITS 32
  
  %define ET_EXEC       2
  %define EM_386        3
  %define EV_CURRENT    1
  
  %define PT_LOAD       1
  %define PT_DYNAMIC    2
  %define PT_INTERP     3
  
  %define PF_X          1
  %define PF_W          2
  %define PF_R          4
  
  %define STT_FUNC      2
  
  %define STB_GLOBAL    1
  
  %define R_386_32      1
  
  %define DT_NULL       0
  %define DT_NEEDED     1
  %define DT_HASH       4
  %define DT_STRTAB     5
  %define DT_SYMTAB     6
  %define DT_STRSZ      10
  %define DT_SYMENT     11
  %define DT_REL        17
  %define DT_RELSZ      18
  %define DT_RELENT     19
  
  %define R_INFO(s, t)    (((s) << 8) | (t))
  
  shentsz       equ     0x28
  
                org     0x15FF0000
  
  ehdr:                                                 ; Elf32_Ehdr
                db      0x7F, "ELF", 1, 1, 1            ;   e_ident
        times 9 db      0
                dw      ET_EXEC                         ;   e_type
                dw      EM_386                          ;   e_machine
                dd      EV_CURRENT                      ;   e_version
                dd      _start                          ;   e_entry
                dd      phdr - $$                       ;   e_phoff
                dd      0                               ;   e_shoff
                dd      0                               ;   e_flags
                dw      ehdrsz                          ;   e_ehsize
                dw      phentsz                         ;   e_phentsize
                dw      3                               ;   e_phnum
                dw      shentsz                         ;   e_shentsize
                dw      0                               ;   e_shnum
                dw      0                               ;   e_shstrndx
  ehdrsz        equ     $ - ehdr
  
  ;; The interpreter segment
  
  interp:       db      '/lib/ld-linux.so.2'
  
  interpsz      equ     $ - interp + 1
  
  ;; The string table
  
  strtab:
                db      0
  libc_name     equ     $ - strtab
                db      'libc.so.6', 0
  exit_name     equ     $ - strtab
                db      '_exit', 0
  strtabsz      equ     $ - strtab
  
  align 4
  
  ;; The relocation table
  
  reltab:                                               ; Elf32_Rel
                dd      exit_ptr                        ;   r_offset
                dd      R_INFO(1, R_386_32)             ;   r_info
  relentsz      equ     $ - reltab
  reltabsz      equ     $ - reltab
  
  ;; The program segment header table, hash table, symbol table,
  ;; and dynamic section.
  
  phdr:                                                 ; Elf32_Phdr
                dd      PT_LOAD                         ;   p_type
                dd      0                               ;   p_offset
                dw      0                               ;   p_vaddr
  part2:        call    [exit_ptr]                      ;   p_paddr
                dd      filesz                          ;   p_filesz
                dd      memsz                           ;   p_memsz
                dd      PF_R | PF_W | PF_X              ;   p_flags
                dd      0x1000                          ;   p_align
  phentsz       equ     $ - phdr
                dd      PT_DYNAMIC                      ;   p_type
                dd      dyntab - $$                     ;   p_offset
                dd      dyntab                          ;   p_vaddr
  _start:       push    byte 42                         ;   p_paddr
                jmp     short part2
                dd      dyntabsz                        ;   p_filesz
                dd      dyntabsz                        ;   p_memsz
                dd      PF_R | PF_W                     ;   p_flags
                dd      4                               ;   p_align


                dd      PT_INTERP                       ;   p_type
                dd      interp - $$                     ;   p_offset
                dd      interp                          ;   p_vaddr
                dd      0                               ;   p_paddr
                dd      interpsz                        ;   p_filesz
                dd      interpsz                        ;   p_memsz
                dd      PF_R                            ;   p_flags
                                                        ;   p_align = 1
  
  hashtab:
                dd      1                               ; no. of buckets
                dd      2                               ; no. of symbols
                dd      1                               ; the bucket: symbol #1
                                                        ; two links, both zero
  
  symtab:                                               ; Elf32_Sym
                dd      0                               ;   st_name
                dd      0                               ;   st_value
                dd      0                               ;   st_size
                db      0                               ;   st_info
                db      0                               ;   st_other
                dw      0                               ;   st_shndx
  symentsz      equ     $ - symtab  
                dd      exit_name                       ;   st_name
                dd      0                               ;   st_value
                dd      0                               ;   st_size
                                                        ;   st_info = 18
                                                        ;   st_other = 0
                                                        ;   st_shndx = 0
  ;; The dynamic section
  
  dyntab:
                dd      DT_RELSZ,  reltabsz
                dd      DT_RELENT, relentsz
                dd      DT_REL,    reltab
                dd      DT_STRSZ,  strtabsz
                dd      DT_STRTAB, strtab
                dd      DT_SYMENT, symentsz
                dd      DT_SYMTAB, symtab
                dd      DT_HASH,   hashtab
                dd      DT_NEEDED
                db      libc_name
  dyntabsz      equ     $ - dyntab + 11
  
  exit_ptr      equ     $ + 11
  _end          equ     $ + 15
  
  ;; End of the file image.
  
  filesz        equ     $ - $$
  memsz         equ     _end - $$
