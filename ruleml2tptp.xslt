<?xml version="1.0" encoding="UTF-8"?>

<xsl:stylesheet version="2.0"
                xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                xmlns:xs="http://www.w3.org/2001/XMLSchema"
                xmlns:r="http://ruleml.org/spec">
  <!-- The input of this translator must be a normalized RuleML instance. -->

  <xsl:param name="tptp-lang" select="'qmf'" as="xs:string" required="no"/>
  <!-- line break -->
  <xsl:param name="nl" select="'&#xA;'" as="xs:string" required="no"/>

  <xsl:output method="text" encoding="UTF-8"/>
  <xsl:strip-space elements="*"/>

  <xsl:template match="comment()" mode="#all">
    <xsl:if test="not(matches(., '^\s*$'))">
      <!-- trim lines -->
      <xsl:variable name="step-trim-ends"
                          select="replace(., '(^[ \t]+)|([ \t]+$)', '')"/>
      <xsl:variable name="step-trim-lines"
                          select="replace($step-trim-ends, '[ \t]*(\r?\n)[ \t]*', '$1')"/>
      <!-- trim first and last lines if they are blank -->
      <xsl:variable name="step-trim-first-blank-line"
                          select="replace($step-trim-lines, '^\r?\n', '')"/>
      <xsl:variable name="step-trim-last-blank-line"
                          select="replace($step-trim-first-blank-line, '\r?\n$', '')"/>
      <!-- insert '% ' -->
      <xsl:variable name="step-insert-spaces"
                          select="replace($step-trim-last-blank-line, '^%', '% ', 'm')"/>
      <xsl:variable name="step-insert-first"
                          select="replace($step-insert-spaces, '^([^%])', '% $1')"/>
      <xsl:variable name="step-insert-last"
                          select="replace($step-insert-first, '(\r?\n)$', '$1% ')"/>
      <xsl:variable name="step-insert"
                          select="replace($step-insert-last, '(\r?\n)([^%])', '$1% $2')"/>
      <xsl:value-of select="$step-insert"/>
      <!-- switch to a new line after the comment -->
      <xsl:value-of select="$nl"/>
    </xsl:if>
  </xsl:template>

  <!-- break the line with indentation -->
  <xsl:template name="break-line">
    <xsl:param name="depth" required="yes" as="xs:integer"/>
    <!-- somtime we need to go backwards some spaces from the indention -->
    <xsl:param name="retreat" select="0" required="no" as="xs:integer"/>

    <xsl:variable name="indent" as="xs:string *">
      <xsl:text>  </xsl:text> <!-- two leading spaces -->
      <xsl:for-each select="1 to $depth">
        <xsl:text>  </xsl:text> <!-- two spaces for every depth -->
      </xsl:for-each>
    </xsl:variable>
    <xsl:value-of select="$nl"/>
    <xsl:value-of select="substring(string-join($indent, ''), $retreat + 1)"/>

  </xsl:template>

  <xsl:template match="r:*">
    <xsl:apply-templates select="r:*"/>
  </xsl:template>

  <xsl:template match="/">
    <xsl:apply-templates select="comment()"/>
    <xsl:apply-templates select="r:RuleML"/>
  </xsl:template>

  <xsl:template match="r:RuleML">
    <xsl:apply-templates select="comment()"/>
    <xsl:apply-templates select="r:act"/>
  </xsl:template>

  <xsl:template match="r:act">
    <xsl:apply-templates select="comment()"/>
    <xsl:apply-templates select="r:Assert | r:Query">
      <xsl:with-param name="act-index" select="@index" tunnel="yes"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template match="r:Assert">
    <xsl:apply-templates select="comment()"/>
    <xsl:apply-templates select="r:formula | r:termula" mode="fof-formula">
      <xsl:with-param name="formula-type" select="local-name()"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template match="r:Query">
    <xsl:apply-templates select="comment()"/>
    <xsl:apply-templates select="r:formula | r:termula" mode="fof-formula">
      <xsl:with-param name="formula-type" select="local-name()"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template match="r:formula | r:termula" mode="fof-formula">
    <xsl:param name="act-index" required="yes" tunnel="yes" as="xs:integer"/>
    <xsl:param name="formula-type" required="yes" as="xs:string"/>
    <xsl:variable name="depth" select="1" as="xs:integer"/>

    <xsl:apply-templates select="comment()"/>

    <xsl:value-of select="$tptp-lang"/>
    <xsl:text>(</xsl:text>
    <!-- formula name -->
    <xsl:value-of select="concat('act', $act-index, '_formula', count(preceding-sibling::r:formula) + count(preceding-sibling::r:termula) + 1)"/>

    <xsl:text>,</xsl:text>
    <!-- formula role -->
    <xsl:choose>
      <xsl:when test="$formula-type = 'Assert'">
        <xsl:text>axiom</xsl:text>
      </xsl:when>
      <xsl:when test="$formula-type = 'Query'">
        <xsl:text>conjecture</xsl:text>
      </xsl:when>
    </xsl:choose>
    <xsl:text>,</xsl:text>

    <xsl:variable name="content-sequence" as="xs:string*">
      <xsl:apply-templates>
        <xsl:with-param name="depth" select="$depth" tunnel="yes"/>
        <!-- this param indicates if the children can break the line at the very
        beginning -->
        <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="content" select="string-join($content-sequence, '')" as="xs:string"/>
    <xsl:variable name="need-extra-parens" select="not(starts-with($content, '( '))" as="xs:boolean"/>

    <xsl:if test="$need-extra-parens">
      <xsl:text>(</xsl:text>
    </xsl:if>
    <xsl:call-template name="break-line">
      <xsl:with-param name="depth" select="$depth"/>
    </xsl:call-template>
    <xsl:value-of select="$content"/>
    <xsl:choose>
      <xsl:when test="$need-extra-parens">
        <xsl:text> )).</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>).</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:value-of select="$nl"/>
    <xsl:value-of select="$nl"/>
  </xsl:template>

  <xsl:template match="r:Forall">
    <xsl:call-template name="quantified">
      <xsl:with-param name="quantifier" select="'!'"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="r:Exists">
    <xsl:call-template name="quantified">
      <xsl:with-param name="quantifier" select="'?'"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="quantified">
    <xsl:param name="depth" required="yes" as="xs:integer" tunnel="yes"/>
    <xsl:param name="line-breaking" required="yes" as="xs:boolean" tunnel="yes"/>
    <xsl:param name="quantifier" required="yes" as="xs:string"/>
    <xsl:param name="last-quantifier-depth" select="-1" required="no" as="xs:integer" tunnel="yes"/>

    <xsl:variable name="final-depth" as="xs:integer">
      <xsl:choose>
        <xsl:when test="$depth = $last-quantifier-depth + 1">
          <xsl:value-of select="$last-quantifier-depth"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$depth"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>

    <xsl:if test="$line-breaking">
      <xsl:call-template name="break-line">
        <xsl:with-param name="depth" select="$final-depth"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:value-of select="$quantifier"/>
    <xsl:text> [</xsl:text>
    <xsl:call-template name="declare-list"/>
    <xsl:text>] :</xsl:text>

    <xsl:variable name="content-sequence" as="xs:string*">
      <xsl:apply-templates select="r:formula | r:termula">
        <xsl:with-param name="depth" select="$final-depth + 1" tunnel="yes"/>
        <xsl:with-param name="line-breaking" select="true()" tunnel="yes"/>
        <xsl:with-param name="last-quantifier-depth" select="$final-depth" tunnel="yes"/>
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:variable name="content" select="string-join($content-sequence, '')" as="xs:string"/>
    <xsl:if test="not(starts-with($content, $nl))">
      <xsl:text> </xsl:text>
    </xsl:if>
    <xsl:value-of select="$content"/>

  </xsl:template>

  <xsl:template match="r:Neg"> <!-- FOL -->
    <xsl:param name="depth" required="yes" as="xs:integer" tunnel="yes"/>
    <xsl:param name="line-breaking" required="yes" as="xs:boolean" tunnel="yes"/>

    <xsl:if test="$line-breaking">
      <xsl:call-template name="break-line">
        <xsl:with-param name="depth" select="$depth"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:text>~ </xsl:text>

    <xsl:apply-templates select="r:strong">
      <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
      <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
    </xsl:apply-templates>

  </xsl:template>

  <xsl:template match="r:Implies">
    <xsl:param name="depth" required="yes" as="xs:integer" tunnel="yes"/>
    <xsl:param name="line-breaking" required="yes" as="xs:boolean" tunnel="yes"/>

    <xsl:if test="$line-breaking">
      <xsl:call-template name="break-line">
        <xsl:with-param name="depth" select="$depth"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:text>( </xsl:text>

    <xsl:choose>
      <xsl:when test="(r:if | r:then)[1] = r:if">
        <xsl:apply-templates select="r:if">
          <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
          <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
        </xsl:apply-templates>

        <xsl:call-template name="break-line">
          <xsl:with-param name="depth" select="$depth"/>
          <xsl:with-param name="retreat" select="1"/>
        </xsl:call-template>
        <xsl:text>=&gt; </xsl:text>

        <xsl:apply-templates select="r:then">
          <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
          <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="r:then">
          <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
          <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
        </xsl:apply-templates>

        <xsl:call-template name="break-line">
          <xsl:with-param name="depth" select="$depth"/>
          <xsl:with-param name="retreat" select="1"/>
        </xsl:call-template>
        <xsl:text>&lt;= </xsl:text>

        <xsl:apply-templates select="r:if">
          <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
          <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
        </xsl:apply-templates>
      </xsl:otherwise>
    </xsl:choose>

    <xsl:text> )</xsl:text>

  </xsl:template>

  <xsl:template match="r:Equivalent"> <!-- FOL -->
    <xsl:param name="depth" required="yes" as="xs:integer" tunnel="yes"/>
    <xsl:param name="line-breaking" required="yes" as="xs:boolean" tunnel="yes"/>

    <xsl:if test="$line-breaking">
      <xsl:call-template name="break-line">
        <xsl:with-param name="depth" select="$depth"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:text>( </xsl:text>

    <xsl:apply-templates select="r:torso[1]">
      <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
      <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
    </xsl:apply-templates>

    <xsl:call-template name="break-line">
      <xsl:with-param name="depth" select="$depth"/>
      <xsl:with-param name="retreat" select="2"/>
    </xsl:call-template>
    <xsl:text>&lt;=&gt; </xsl:text>

    <xsl:apply-templates select="r:torso[last()]">
      <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
      <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
    </xsl:apply-templates>

    <xsl:text> )</xsl:text>

  </xsl:template>

  <xsl:template match="r:Equal">
    <xsl:apply-templates select="r:left"/>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="r:right"/>
  </xsl:template>

  <xsl:template match="r:And">
    <xsl:call-template name="associated">
      <xsl:with-param name="connective" select="'&amp;'"/>
      <xsl:with-param name="empty-form" select="'$true'"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="r:Or">
    <xsl:call-template name="associated">
      <xsl:with-param name="connective" select="'|'"/>
      <xsl:with-param name="empty-form" select="'$false'"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="associated">
    <xsl:param name="depth" required="yes" as="xs:integer" tunnel="yes"/>
    <xsl:param name="line-breaking" required="yes" as="xs:boolean" tunnel="yes"/>
    <xsl:param name="connective" required="yes" as="xs:string"/>
    <xsl:param name="empty-form" required="yes" as="xs:string"/>
    <xsl:variable name="termulas" select="r:formula | r:termula"/>

    <xsl:choose>
      <xsl:when test="count($termulas) > 1">
        <xsl:if test="$line-breaking">
          <xsl:call-template name="break-line">
            <xsl:with-param name="depth" select="$depth"/>
          </xsl:call-template>
        </xsl:if>
        <xsl:text>( </xsl:text>
        <xsl:for-each select="$termulas">
          <xsl:if test="preceding-sibling::r:formula | preceding-sibling::r:termula">
            <xsl:call-template name="break-line">
              <xsl:with-param name="depth" select="$depth"/>
            </xsl:call-template>
            <xsl:value-of select="$connective"/>
            <xsl:text> </xsl:text>
          </xsl:if>
          <xsl:apply-templates>
            <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
            <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
          </xsl:apply-templates>
        </xsl:for-each>
        <xsl:text> )</xsl:text>
      </xsl:when>
      <xsl:when test="r:formula | r:termula">
        <xsl:apply-templates>
          <xsl:with-param name="depth" select="$depth + 1" tunnel="yes"/>
          <xsl:with-param name="line-breaking" select="false()" tunnel="yes"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:value-of select="$empty-form"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="r:Atom | r:Expr"> <!-- Expr is in Hornlog. -->
    <xsl:apply-templates select="r:op"/>
    <!-- sorted args -->
    <xsl:for-each select="r:arg">
      <xsl:choose>
        <xsl:when test="preceding-sibling::r:arg">
            <xsl:choose>
			   <xsl:when test="child::r:Data"></xsl:when>
			   <xsl:otherwise>
				 <xsl:text>,</xsl:text>
			   </xsl:otherwise>
			 </xsl:choose>
		</xsl:when>
        <xsl:otherwise>
          <xsl:text>(</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:apply-templates select="r:Ind | r:Var | r:Expr"/>
      <xsl:if test="not(following-sibling::r:arg)">
        <xsl:text>)</xsl:text>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- variables in the TPTP language start with a uppercase letter -->
  <xsl:template match="r:Var">
    <xsl:variable name="normalized-text" select="normalize-space(text())" as="xs:string"/>
    <xsl:value-of select="concat(upper-case(substring($normalized-text, 1, 1)), substring($normalized-text, 2))"/>
  </xsl:template>

  <!-- constants and functors in the TPTP language start with a lowercase letter or is single-quoted -->
  <xsl:template match="r:Rel | r:Ind | r:Fun | r:Const"> <!-- Fun is in Hornlog. -->
    <xsl:choose>
      <xsl:when test="string(@iri)">
        <xsl:call-template name="normalize-text">
          <xsl:with-param name="text" select="@iri"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="normalize-text">
          <xsl:with-param name="text" select="string(text())"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- a comma-separated list of declarations -->
  <xsl:template name="declare-list">
    <xsl:for-each select="r:declare">
      <xsl:if test="preceding-sibling::r:declare">
        <xsl:text>,</xsl:text>
      </xsl:if>
      <xsl:apply-templates select="r:*"/>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="normalize-text">
    <xsl:param name="text" required="yes" as="xs:string"/>

    <xsl:variable name="normalized-text" select="normalize-space($text)" as="xs:string"/>
    <xsl:choose>
      <xsl:when test="matches($normalized-text, '^[a-z][a-z0-9_]*$', 'i')">
        <xsl:value-of select="concat(lower-case(substring($normalized-text, 1, 1)), substring($normalized-text, 2))"/>
      </xsl:when>
      <xsl:otherwise>
        <!-- escape \ and ' then single quote -->
        <xsl:value-of select='concat("&apos;",
        replace(replace($text, "\\", "\\\\"), "&apos;", "\\&apos;"), "&apos;")'/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>


  <!-- Higher Order -->

  <xsl:template match="r:Uniterm">
    <xsl:text>(</xsl:text>
    <xsl:call-template name="join">
      <xsl:with-param name="list" select="r:*"/>
      <xsl:with-param name="separator" select="' @ '" />
    </xsl:call-template>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <xsl:template match="r:Lambda">
    <xsl:text>(</xsl:text>
    <xsl:text>^ [</xsl:text>
    <xsl:call-template name="join">
      <xsl:with-param name="list" select="r:declare" />
      <xsl:with-param name="separator" select="','" />
    </xsl:call-template>
    <xsl:text>] : </xsl:text>
    <xsl:apply-templates select="r:termula"/>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <xsl:template match="r:Entitype">
    <xsl:apply-templates select="r:entity"/>
    <xsl:text>:</xsl:text>
    <xsl:apply-templates select="r:type"/>
  </xsl:template>

  <xsl:template match="r:Tmap">
    <xsl:text>(</xsl:text>
    <xsl:apply-templates select="r:domain"/>
    <xsl:text>&gt;</xsl:text>
    <xsl:apply-templates select="r:codomain"/>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <xsl:template match="r:Tbase">
    <xsl:text>$</xsl:text>
    <xsl:value-of select="text()"/>
  </xsl:template>


  <!-- Modal -->

  <xsl:template match="r:Modal">
    <xsl:text>(</xsl:text>
    <xsl:apply-templates select="r:variety"/>
    <xsl:text>:</xsl:text>
    <xsl:text>(</xsl:text> <!-- This pair of parens is required by THF but not FOL. Put them here as a interim solution. -->
    <xsl:apply-templates select="r:proposition"/>
    <xsl:text>)</xsl:text>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <xsl:template match="r:Box">
    <xsl:text>#box</xsl:text>
  </xsl:template>

  <xsl:template match="r:Dia">
    <xsl:text>#dia</xsl:text>
  </xsl:template>


  <!-- Utilities -->

  <xsl:template name="join">
    <xsl:param name="list"/>
    <xsl:param name="separator" as="xs:string"/>

    <xsl:for-each select="$list">
      <xsl:apply-templates/>
      <xsl:if test="position() != last()">
        <xsl:value-of select="$separator"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

</xsl:stylesheet>
