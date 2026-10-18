import { defineConfig } from 'vitepress'

export default defineConfig({
  title: "SF-lean4",
  description: "《软件基础》(Software Foundations) 现代 Lean 4 中文社区重制版",
  base: process.env.GITHUB_ACTIONS ? '/SF-lean4/' : '/',
  
  head: [
    ['link', { rel: 'icon', href: '/logo.svg' }]
  ],
  
  markdown: {
    math: true,
    config: (md) => {
      const defaultCodeInline = md.renderer.rules.code_inline;
      md.renderer.rules.code_inline = (tokens, idx, options, env, slf) => {
        tokens[idx].attrSet('v-pre', '');
        return defaultCodeInline
          ? defaultCodeInline(tokens, idx, options, env, slf)
          : slf.renderToken(tokens, idx, options);
      };
    }
  },

  themeConfig: {
    logo: '/logo.svg',
    siteTitle: 'SF-lean4 软件基础',
    
    search: {
      provider: 'local',
      options: {
        locales: {
          root: {
            translations: {
              button: {
                buttonText: '搜索文档或定理...',
                buttonAriaLabel: '搜索文档或定理'
              },
              modal: {
                noResultsText: '无法找到相关结果',
                resetButtonTitle: '清除查询条件',
                footer: {
                  selectText: '选择',
                  navigateText: '切换',
                  closeText: '关闭'
                }
              }
            }
          }
        }
      }
    },

    nav: [
      { text: '卷一：逻辑基础 (LF)', link: '/LF/Basics' },
      { text: '卷二：语言基础 (PLF)', link: '/PLF/Preface' },
      { text: '卷三：算法验证 (VFA)', link: '/VFA/Preface' },
      { 
        text: '资源与链接',
        items: [
          { text: 'GitHub 仓库', link: 'https://github.com/Ghost-Silver/SF-lean4' },
          { text: '原版 Software Foundations', link: 'https://softwarefoundations.cis.upenn.edu/' },
          { text: 'Lean 4 官方文档', link: 'https://lean-lang.org/' }
        ]
      }
    ],

    sidebar: {
      '/LF/': [
        {
          text: '卷一：逻辑基础 (LF)',
          collapsed: false,
          items: [
            { text: 'Basics · 基础篇：函数式编程与基础策略', link: '/LF/Basics' },
            { text: 'Induction · 归纳证明：数学归纳法与规范化', link: '/LF/Induction' },
            { text: 'Lists · 结构化数据：列表与多态映射', link: '/LF/Lists' },
            { text: 'Poly · 多态与高阶函数：Church 数', link: '/LF/Poly' },
            { text: 'Tactics · 策略进阶：反演、代换与泛化', link: '/LF/Tactics' },
            { text: 'Logic · 形式逻辑：构造性命题与联结词', link: '/LF/Logic' },
            { text: 'IndProp · 归纳命题与关系：置换与正则导数', link: '/LF/IndProp' },
            { text: 'Maps · 函数映射模型：全映射与偏映射', link: '/LF/Maps' },
            { text: 'ProofObjects · 柯里-霍华德同构：证明即程序', link: '/LF/ProofObjects' },
            { text: 'IndPrinciples · 归纳法则深入：原理与自定义模式', link: '/LF/IndPrinciples' },
            { text: 'Rel · 二元关系：性质与自反传递闭包', link: '/LF/Rel' },
            { text: 'Imp · 命令式语言 Imp：语法与大步语义', link: '/LF/Imp' },
            { text: 'ImpParser · 词法分析与语法分析器', link: '/LF/ImpParser' },
            { text: 'ImpCEvalFun · 求值函数与语义等价性', link: '/LF/ImpCEvalFun' },
            { text: 'Extraction · 代码抽取与编译执行', link: '/LF/Extraction' },
            { text: 'Auto · 自动化证明策略与搜索', link: '/LF/Auto' },
            { text: 'AltAuto · 自动化精粹与模式匹配', link: '/LF/AltAuto' },
            { text: 'Postscript · 全卷后记：理论回顾', link: '/LF/Postscript' },
            { text: 'Bib · 参考文献数据库', link: '/LF/Bib' },
          ]
        }
      ],
      '/PLF/': [
        {
          text: '卷二：编程语言基础 (PLF)',
          collapsed: false,
          items: [
            { text: 'Preface · 前言与课程路线图', link: '/PLF/Preface' },
            { text: 'Maps · 映射库桥接', link: '/PLF/Maps' },
            { text: 'Imp · Imp 语言桥接', link: '/PLF/Imp' },
            { text: 'Equiv · 程序等价性：同余性与常量折叠', link: '/PLF/Equiv' },
            { text: 'Hoare · 霍尔逻辑 (I)：三元组与推理规则', link: '/PLF/Hoare' },
            { text: 'Hoare2 · 霍尔逻辑 (II)：VCGen 验证条件生成', link: '/PLF/Hoare2' },
            { text: 'HoareAsLogic · 作为逻辑的霍尔系统：可靠与完备', link: '/PLF/HoareAsLogic' },
            { text: 'Smallstep · 小步操作语义与多步闭包', link: '/PLF/Smallstep' },
            { text: 'Types · 类型系统入门：非类型化算术与健全性', link: '/PLF/Types' },
            { text: 'Stlc · 简单类型 Lambda 演算 (STLC)', link: '/PLF/Stlc' },
            { text: 'StlcProp · STLC 性质：进益、保型与类型安全', link: '/PLF/StlcProp' },
            { text: 'MoreStlc · STLC 扩充：自然数、和积与定点', link: '/PLF/MoreStlc' },
            { text: 'Sub · 子类型化：包容法则与函数逆变', link: '/PLF/Sub' },
            { text: 'Typechecking · 类型检查器可判定算法', link: '/PLF/Typechecking' },
            { text: 'Records · 记录类型系统与字段投影', link: '/PLF/Records' },
            { text: 'References · 可变状态与堆内存引用', link: '/PLF/References' },
            { text: 'RecordSub · 记录子类型化：宽度、深度与置换', link: '/PLF/RecordSub' },
            { text: 'Norm · STLC 强规范化与停机证明', link: '/PLF/Norm' },
            { text: 'PE · 偏评估、符号执行与在线特化', link: '/PLF/PE' },
            { text: 'Postscript · 全卷后记与工业应用全景', link: '/PLF/Postscript' },
            { text: 'Bib · 参考文献库', link: '/PLF/Bib' },
          ]
        }
      ],
      '/VFA/': [
        {
          text: '卷三：函数式算法验证 (VFA)',
          collapsed: false,
          items: [
            { text: 'Preface · 全书前言：算法形式化验证', link: '/VFA/Preface' },
            { text: 'Perm · 数值比较与置换：omega 决策过程', link: '/VFA/Perm' },
            { text: 'Sort · 插入排序及其形式化全规约', link: '/VFA/Sort' },
            { text: 'Multiset · 多重集模型与内容计数', link: '/VFA/Multiset' },
            { text: 'BagPerm · 基于包的多重集置换等价性', link: '/VFA/BagPerm' },
            { text: 'Selection · 选择排序：燃油与度量良基递归', link: '/VFA/Selection' },
            { text: 'Merge · 归并排序：双步列表归纳与对数分治', link: '/VFA/Merge' },
            { text: 'Maps · 全映射与偏映射函数模型', link: '/VFA/Maps' },
            { text: 'SearchTree · 二叉搜索树 BST 与抽象模型', link: '/VFA/SearchTree' },
            { text: 'ADT · 抽象数据类型规范与队列 ADT', link: '/VFA/ADT' },
            { text: 'Extract · 机器整数公理化抽象与抽取', link: '/VFA/Extract' },
            { text: 'Redblack · Okasaki 红黑树与平衡对数界限', link: '/VFA/Redblack' },
            { text: 'Trie · 前缀树查找表与正数二进制算术', link: '/VFA/Trie' },
            { text: 'Priqueue · 优先队列 ADT 规范与参考实现', link: '/VFA/Priqueue' },
            { text: 'Binom · 二项堆：可合并队列与进位链', link: '/VFA/Binom' },
            { text: 'Decide · 判定过程：反射与构造性析取', link: '/VFA/Decide' },
            { text: 'Color · 图着色与编译器寄存器分配', link: '/VFA/Color' },
          ]
        }
      ]
    },

    socialLinks: [
      { icon: 'github', link: 'https://github.com/Ghost-Silver/SF-lean4' }
    ],

    outline: {
      level: [2, 3],
      label: '本页导读大纲'
    },

    docFooter: {
      prev: '上一章',
      next: '下一章'
    },

    footer: {
      message: '基于 MIT 与 Software Foundations 原版教育许可协议开源',
      copyright: 'Copyright © 2024-2026 Ghost-Silver · Software Foundations Authors'
    }
  }
})
