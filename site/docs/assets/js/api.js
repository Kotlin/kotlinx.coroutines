/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */


function addTag(rowElement, tag) {
    var tags = $(rowElement).find('.tags');
    if (tags.length == 0) {
        tags = $('<div class="tags"></div>');
        $(rowElement).find('td:first').append(tags);
    }
    tags.append('<div class="tags__tag">' + tag + '</div>')
}

$(document).ready(function () {
    $('[data-platform]').each(function (ind, element) {
        var platform = element.getAttribute('data-platform');
        addTag(element, platform)
    });
});
