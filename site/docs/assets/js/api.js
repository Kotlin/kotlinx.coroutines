/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
