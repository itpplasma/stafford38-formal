// Keep the optional-variant selector out of maps that have no variant cards.
export function reviewScopeOptions(items) {
  const hasVariants = items.some((item) => (item.review_scope ?? 'publication') === 'alternative');
  return '<option value="publication">Whole paper correspondence (default)</option>' +
    (hasVariants ? '<option value="alternative">Optional proof variants</option>' : '') +
    '<option value="all">All reference material</option>';
}
