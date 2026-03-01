/* ═══════════════════════════════════════
   ショップ品揃え
   各ショップIDに対応する商品リスト
   items: [{id, isEquip}]
   ═══════════════════════════════════════ */
const SHOPS = {
  town1_general: {
    name: 'よろずや',
    items: [
      { id:'wooden_stick', isEquip:true },
      { id:'copper_sword', isEquip:true },
      { id:'dagger',       isEquip:true },
      { id:'wooden_staff', isEquip:true },
      { id:'cloth',        isEquip:true },
      { id:'leather',      isEquip:true },
      { id:'robe',         isEquip:true },
      { id:'herb',         isEquip:false },
      { id:'antidote',     isEquip:false },
    ],
  },
  port_weapon: {
    name: '武器屋',
    items: [
      { id:'iron_sword',   isEquip:true },
      { id:'ninja_blade',  isEquip:true },
      { id:'magic_staff',  isEquip:true },
    ],
  },
  port_armor: {
    name: '防具屋',
    items: [
      { id:'chainmail',   isEquip:true },
      { id:'ninja_garb',  isEquip:true },
      { id:'magic_robe',  isEquip:true },
    ],
  },
  port_item: {
    name: 'アイテム屋',
    items: [
      { id:'herb',        isEquip:false },
      { id:'hi_herb',     isEquip:false },
      { id:'magic_water', isEquip:false },
      { id:'antidote',    isEquip:false },
      { id:'tent',        isEquip:false },
    ],
  },
  mine_general: {
    name: 'よろずや',
    items: [
      { id:'steel_sword',   isEquip:true },
      { id:'sage_staff',    isEquip:true },
      { id:'iron_armor',    isEquip:true },
      { id:'mithril_sword', isEquip:true },
      { id:'mithril_armor', isEquip:true },
      { id:'power_ring',    isEquip:true },
      { id:'guard_ring',    isEquip:true },
      { id:'magic_amulet',  isEquip:true },
      { id:'swift_boots',   isEquip:true },
      { id:'hp_ring',       isEquip:true },
      { id:'hi_herb',       isEquip:false },
      { id:'elixir',        isEquip:false },
      { id:'magic_water',   isEquip:false },
      { id:'tent',          isEquip:false },
    ],
  },
  elf_weapon: {
    name: '武器屋',
    items: [
      { id:'elf_bow',       isEquip:true },
      { id:'spirit_staff',  isEquip:true },
      { id:'mithril_sword', isEquip:true },
    ],
  },
  elf_armor: {
    name: '防具屋',
    items: [
      { id:'elf_robe',     isEquip:true },
      { id:'spirit_armor', isEquip:true },
      { id:'mithril_armor', isEquip:true },
    ],
  },
  elf_item: {
    name: 'アイテム屋',
    items: [
      { id:'hi_herb',      isEquip:false },
      { id:'elixir',       isEquip:false },
      { id:'magic_water',  isEquip:false },
      { id:'tent',         isEquip:false },
    ],
  },
  last_weapon: {
    name: '武器屋',
    items: [
      { id:'mithril_sword', isEquip:true },
      { id:'spirit_staff',  isEquip:true },
      { id:'elf_bow',       isEquip:true },
    ],
  },
  last_armor: {
    name: '防具屋',
    items: [
      { id:'mithril_armor', isEquip:true },
      { id:'spirit_armor',  isEquip:true },
      { id:'elf_robe',      isEquip:true },
    ],
  },
  last_item: {
    name: 'アイテム屋',
    items: [
      { id:'elixir',       isEquip:false },
      { id:'hi_herb',      isEquip:false },
      { id:'magic_water',  isEquip:false },
      { id:'tent',         isEquip:false },
      { id:'world_branch', isEquip:false },
    ],
  },
};
